import {
  CONFIG,
  cumulativeDistances,
  indexAtFraction,
  buildDistanceBasedCheckpoints,
  evaluate,
} from './matching.js';

const MAPS_API_KEY =
  'AIzaSyAHf84f7w_OrzWnPx0VWRtMlx3oQy5mADM';
const AUTH_PASSWORD = 'visions';

const CAR_A_INITIAL_PROGRESS = 0.00;
const STEP_MS = 500;
const BASE_STEP_SEC = 5;
const LOG_INTERVAL_SIM_SEC = 10;
const CANDIDATE_TARGET_COUNT = 30;
const CANDIDATE_BATCH_SIZE = 3;
const CANDIDATE_BATCH_DELAY_MS = 350;
const CANDIDATE_RETRY_BASE_DELAY_MS = 450;

const authElements = {
  screen: document.getElementById('auth-screen'),
  form: document.getElementById('auth-form'),
  input: document.getElementById('password-input'),
  error: document.getElementById('auth-error'),
};

function setAuthError(message) {
  if (!authElements.error) {
    return;
  }

  authElements.error.textContent = message;
}

function handleAuthSubmit(event) {
  event.preventDefault();

  const inputValue = authElements.input?.value.trim() ?? '';

  if (!inputValue) {
    setAuthError('パスワードを入力してください。');
    authElements.input?.focus();
    return;
  }

  if (inputValue !== AUTH_PASSWORD) {
    setAuthError('パスワードが違います。');
    authElements.input?.focus();
    authElements.input?.select();
    return;
  }

  document.body.classList.add('authenticated');
  setAuthError('');
  main();
}

const $ = id =>
  document.getElementById(id);

const el = {
  status: $('status-pill'),
  generate: $('generate-btn'),
  start: $('start-btn'),
  pause: $('pause-btn'),
  reset: $('reset-btn'),
  speed: $('speed-select'),

  originInput: $('origin-input'),
  destinationInput: $('destination-input'),

  origin: $('origin-value'),
  destination: $('destination-value'),
  routeDistance: $('route-distance'),
  divisionCount: $('division-count'),
  checkpointCount: $('checkpoint-count'),

  simTime: $('sim-time'),
  aProgress: $('a-progress'),
  aPosition: $('a-position'),
  matchCount: $('match-count'),
  bestScore: $('best-score'),
  systemMode: $('system-mode'),
  lastUpdate: $('last-update'),

  logSnapshotCount: $('log-snapshot-count'),
  logRowCount: $('log-row-count'),
  exportCsv: $('export-csv-btn'),

  checkpointList: $('checkpoint-list'),
  candidateList: $('candidate-list'),
  vehicleDetail: $('vehicle-detail'),
  parameterInfo: $('parameter-info'),
  themeToggle: $('theme-toggle-btn'),
  panelClose: $('panel-close-btn'),
  panelOpen: $('panel-open-btn'),
};

const typeNames = {
  leading_same_route: '同一経路・先行車',
  trailing_same_route: '同一経路・後続車',
  merge_midway: '途中合流車',
  leave_midway: '途中離脱車',
  unrelated: '無関係車',
};

let map;
let directionsService;
let directionsRenderer;
let originAutocomplete;
let destinationAutocomplete;

let route = [];
let baseCum = [];
let routeDurationSeconds = 0;
let checkpoints = [];
let divisions = 0;
let userA = null;

let elapsed = 0;
let timer = null;
let generationInProgress = false;

// 時系列分析ログ（シミュレーション時間ベース）
let simulationLog = [];
let nextLogElapsed = 0;
let loggedSnapshotTimes = new Set();
let experimentMeta = null;

let aMarker = null;
let originMarker = null;
let destinationMarker = null;
let cpMarkers = [];

const states = new Map();
const candidateMarkers = new Map();
const candidateLines = new Map();
const commonCpHighlights = new Map();

function setStatus(
  message,
  error = false
) {
  el.status.textContent = message;
  el.status.classList.toggle(
    'error',
    error
  );
}

function latLngObject(point) {
  if (Array.isArray(point)) {
    return {
      lat: Number(point[0]),
      lng: Number(point[1]),
    };
  }

  if (typeof point.lat === 'function') {
    return {
      lat: point.lat(),
      lng: point.lng(),
    };
  }

  return {
    lat: Number(point.lat),
    lng: Number(point.lng),
  };
}

function escapeHtml(value) {
  return String(value).replace(
    /[&<>"']/g,
    ch => ({
      '&': '&amp;',
      '<': '&lt;',
      '>': '&gt;',
      '"': '&quot;',
      "'": '&#39;',
    }[ch])
  );
}

const f3 = value =>
  Number.isFinite(value)
    ? value.toFixed(3)
    : '—';

const fm = value =>
  Number.isFinite(value)
    ? `${value.toFixed(2)} 分`
    : '—';

const fk = value =>
  Number.isFinite(value)
    ? `${value.toFixed(3)} km`
    : '—';

function markerIcon(
  color,
  scale = 8
) {
  return {
    path:
      google.maps.SymbolPath.CIRCLE,

    scale,

    fillColor:
      color,

    fillOpacity:
      1,

    strokeColor:
      '#ffffff',

    strokeWeight:
      2,
  };
}

async function loadGoogleMaps() {
  await new Promise(
    (resolve, reject) => {
      window.initDriveriaMap =
        resolve;

      const script =
        document.createElement(
          'script'
        );

      script.src =
        `https://maps.googleapis.com/maps/api/js?key=${encodeURIComponent(MAPS_API_KEY)}&libraries=geometry,places&callback=initDriveriaMap`;

      script.async = true;
      script.defer = true;

      script.onerror =
        () => reject(
          new Error(
            'Google Maps API の読み込みに失敗しました．'
          )
        );

      document.head.appendChild(
        script
      );
    }
  );
}

function initMap() {
  map =
    new google.maps.Map(
      $('map'),
      {
        center: {
          lat: 35.69,
          lng: 139.48,
        },

        zoom: 13,
        streetViewControl: false,
        mapTypeControl: false,
        fullscreenControl: true,
      }
    );

  directionsService =
    new google.maps.DirectionsService();

  directionsRenderer =
    new google.maps.DirectionsRenderer({
      map,

      suppressMarkers:
        true,

      polylineOptions: {
        strokeColor:
          '#00a8ff',

        strokeOpacity:
          0.95,

        strokeWeight:
          6,

        zIndex:
          30,
      },
    });

  originAutocomplete =
    new google.maps.places.Autocomplete(
      el.originInput,
      {
        fields: [
          'geometry',
          'name',
          'formatted_address',
        ],
      }
    );

  destinationAutocomplete =
    new google.maps.places.Autocomplete(
      el.destinationInput,
      {
        fields: [
          'geometry',
          'name',
          'formatted_address',
        ],
      }
    );
}

function requestGoogleRoute() {
  const originText =
    el.originInput.value.trim();

  const destinationText =
    el.destinationInput.value.trim();

  if (!originText || !destinationText) {
    throw new Error(
      '出発地と目的地を入力してください．'
    );
  }

  const originPlace =
    originAutocomplete?.getPlace();

  const destinationPlace =
    destinationAutocomplete?.getPlace();

  const origin =
    originPlace?.geometry?.location
    || originText;

  const destination =
    destinationPlace?.geometry?.location
    || destinationText;

  return new Promise(
    (resolve, reject) => {
      directionsService.route(
        {
          origin,
          destination,

          travelMode:
            google.maps.TravelMode.DRIVING,

          provideRouteAlternatives:
            false,
        },

        (
          result,
          status
        ) => {
          if (
            status !== 'OK'
            ||
            !result?.routes?.length
          ) {
            reject(
              new Error(
                `Directions API: ${status}`
              )
            );

            return;
          }

          resolve(result);
        }
      );
    }
  );
}

function sampleRoute(
  path,
  targetSpacingMeters = 40
) {
  const sampled = [
    latLngObject(path[0]),
  ];

  for (
    let i = 1;
    i < path.length;
    i += 1
  ) {
    const a = path[i - 1];
    const b = path[i];

    const distance =
      google.maps.geometry
        .spherical
        .computeDistanceBetween(
          a,
          b
        );

    const pieces =
      Math.max(
        1,
        Math.ceil(
          distance
          / targetSpacingMeters
        )
      );

    for (
      let j = 1;
      j <= pieces;
      j += 1
    ) {
      sampled.push(
        latLngObject(
          google.maps.geometry
            .spherical
            .interpolate(
              a,
              b,
              j / pieces
            )
        )
      );
    }
  }

  return sampled;
}

function pointAtRouteFraction(fraction) {
  return route[indexAtFraction(baseCum, Math.max(0, Math.min(1, fraction)))];
}

function offsetPoint(point, offset = [0, 0]) {
  const lat = Number(point.lat);
  const lng = Number(point.lng);
  return {
    lat: lat + Number(offset[0] || 0),
    lng: lng + Number(offset[1] || 0),
  };
}

function routeHeadingAtFraction(fraction) {
  const center = indexAtFraction(
    baseCum,
    Math.max(0, Math.min(1, Number(fraction)))
  );
  const fromIndex = Math.max(0, center - 4);
  const toIndex = Math.min(route.length - 1, center + 4);
  const from = route[fromIndex];
  const to = route[toIndex];

  if (!from || !to || fromIndex === toIndex) {
    return 0;
  }

  return google.maps.geometry.spherical.computeHeading(
    new google.maps.LatLng(from.lat, from.lng),
    new google.maps.LatLng(to.lat, to.lng)
  );
}

function offsetPointMeters(point, distanceMeters, headingDegrees) {
  const shifted = google.maps.geometry.spherical.computeOffset(
    new google.maps.LatLng(Number(point.lat), Number(point.lng)),
    Math.max(0, Number(distanceMeters) || 0),
    Number(headingDegrees) || 0
  );
  return latLngObject(shifted);
}

function resolveRoutePlanNode(node) {
  const fraction = Math.max(0, Math.min(1, Number(node.fraction ?? 0)));
  const basePoint = pointAtRouteFraction(fraction);

  if (node.kind === 'a') {
    return basePoint;
  }

  if (node.kind === 'cardinal') {
    return offsetPointMeters(
      basePoint,
      Number(node.distanceKm || 0) * 1000,
      Number(node.heading || 0)
    );
  }

  if (node.kind === 'normal') {
    const heading = routeHeadingAtFraction(fraction);
    const side = Number(node.side || 1) >= 0 ? 1 : -1;
    return offsetPointMeters(
      basePoint,
      Number(node.distanceKm || 0) * 1000,
      heading + side * 90
    );
  }

  throw new Error(`Unknown route plan node: ${node.kind}`);
}

function sleep(ms) {
  return new Promise(resolve => window.setTimeout(resolve, ms));
}

function compactRoutePlan(plan, mode = 'full') {
  if (mode === 'full' || plan.length <= 2) {
    return plan;
  }

  // 以前は「6点以下なら簡略化しない」ため、user12 / user18 のような
  // 5点構成では再試行しても全く同じDirectionsリクエストになっていた。
  // reduced / minimal では点数に関係なくwaypointを減らし、取得成功率を上げる。
  const first = plan[0];
  const last = plan[plan.length - 1];
  const middle = plan.slice(1, -1);
  if (!middle.length) return [first, last];

  const aNodes = middle.filter(node => node.kind === 'a');
  const externalNodes = middle.filter(node => node.kind !== 'a');

  if (mode === 'minimal') {
    // 合流・離脱・交差というシナリオの核になるA接触点を優先して1点残す。
    const pivot = aNodes.length
      ? aNodes[Math.floor((aNodes.length - 1) / 2)]
      : middle[Math.floor((middle.length - 1) / 2)];
    return [first, pivot, last];
  }

  // reduced: A上の接触点を優先しつつ、最大2 waypointまで残す。
  const selected = [];
  const addUnique = node => {
    if (node && !selected.includes(node)) selected.push(node);
  };

  if (aNodes.length) {
    addUnique(aNodes[0]);
    addUnique(aNodes[aNodes.length - 1]);
  }
  if (externalNodes.length && selected.length < 2) {
    addUnique(externalNodes[Math.floor((externalNodes.length - 1) / 2)]);
  }
  if (selected.length < 2) {
    addUnique(middle[Math.floor((middle.length - 1) / 2)]);
  }

  selected.sort((x, y) => middle.indexOf(x) - middle.indexOf(y));
  return [first, ...selected.slice(0, 2), last];
}

function candidateDirectionsRequest(
  definition,
  { mode = 'full', distanceScale = 1 } = {}
) {
  const plan = compactRoutePlan(definition.routePlan || [], mode);
  if (plan.length < 2) {
    throw new Error(`${definition.id}: routePlan must contain at least 2 points`);
  }

  const scale = Math.max(0.20, Math.min(1, Number(distanceScale) || 1));
  const scaledPlan = plan.map(node => {
    if (node.kind === 'a') return { ...node };
    return {
      ...node,
      distanceKm: Number(node.distanceKm || 0) * scale,
    };
  });

  const points = scaledPlan.map(resolveRoutePlanNode);
  const origin = points[0];
  const destination = points[points.length - 1];
  const waypoints = points.slice(1, -1).map(location => ({
    location,
    stopover: false,
  }));

  return {
    origin,
    destination,
    travelMode: google.maps.TravelMode.DRIVING,
    optimizeWaypoints: false,
    provideRouteAlternatives: false,
    waypoints,
  };
}

class CandidateDirectionsError extends Error {
  constructor(id, status) {
    super(`${id}: Directions API ${status}`);
    this.name = 'CandidateDirectionsError';
    this.status = status;
  }
}

function requestCandidateRoadRoute(definition, options = {}) {
  return new Promise((resolve, reject) => {
    directionsService.route(
      candidateDirectionsRequest(definition, options),
      (result, status) => {
        if (status !== 'OK' || !result?.routes?.length) {
          reject(new CandidateDirectionsError(definition.id, status));
          return;
        }

        const apiRoute = result.routes[0];
        const legs = apiRoute.legs || [];
        resolve({
          route: sampleRoute(apiRoute.overview_path, 40),
          distanceMeters: legs.reduce(
            (sum, leg) => sum + Number(leg.distance?.value || 0),
            0
          ),
          durationSeconds: legs.reduce(
            (sum, leg) => sum + Number(leg.duration?.value || 0),
            0
          ),
        });
      }
    );
  });
}

function isTransientDirectionsStatus(status) {
  return status === 'OVER_QUERY_LIMIT' || status === 'UNKNOWN_ERROR';
}

async function requestCandidateRoadRouteRobust(definition) {
  // 走行パターンを維持しながら段階的に条件を緩める。
  // Route値を固定したり、失敗車両をCar Aの経路で代用したりはしない。
  const strategies = [
    { mode: 'full',    distanceScale: 1.00, label: 'full-100%' },
    { mode: 'reduced', distanceScale: 1.00, label: 'reduced-100%' },
    { mode: 'full',    distanceScale: 0.80, label: 'full-80%' },
    { mode: 'reduced', distanceScale: 0.80, label: 'reduced-80%' },
    { mode: 'minimal', distanceScale: 0.80, label: 'minimal-80%' },
    { mode: 'reduced', distanceScale: 0.60, label: 'reduced-60%' },
    { mode: 'minimal', distanceScale: 0.60, label: 'minimal-60%' },
    { mode: 'minimal', distanceScale: 0.40, label: 'minimal-40%' },
  ];

  let lastError = null;

  for (let strategyIndex = 0; strategyIndex < strategies.length; strategyIndex += 1) {
    const strategy = strategies[strategyIndex];
    const maxAttempts = 3;

    for (let attempt = 1; attempt <= maxAttempts; attempt += 1) {
      try {
        const result = await requestCandidateRoadRoute(definition, strategy);
        return {
          ...result,
          generationStrategy: strategy.label,
          generationAttempt: attempt,
        };
      } catch (error) {
        lastError = error;
        const status = error?.status || 'UNKNOWN';
        console.warn(
          `${definition.id}: ${strategy.label} / attempt ${attempt} failed (${status})`
        );

        // 一時的なAPIエラーのみ同じ条件で再試行する。
        if (isTransientDirectionsStatus(status) && attempt < maxAttempts) {
          await sleep(
            CANDIDATE_RETRY_BASE_DELAY_MS * Math.pow(2, attempt - 1)
          );
          continue;
        }

        // ZERO_RESULTS等は、次の「より単純・近距離」の戦略へ移る。
        break;
      }
    }

    if (strategyIndex < strategies.length - 1) {
      await sleep(CANDIDATE_RETRY_BASE_DELAY_MS);
    }
  }

  throw new Error(
    `${definition.id}: 全ての経路取得戦略に失敗しました`
    + (lastError ? ` (${lastError.message})` : '')
  );
}

function resolveCandidateInitialProgress({
  progress,
  useBaseRoute,
  targetLeadDeltaMin,
}) {
  // Car Aを0%から開始する本実験では，同一路線の先行車1〜3は
  // Car Aと同程度の平均速度で走るものとして，目標先行時間を距離進捗へ変換する。
  // CP1より先にいる車両は，その時点で次の将来共通CPを評価するため，
  // 32%への人工的な上限制約は設けない。
  if (useBaseRoute) {
    const aEtaMinutes = Math.max(1e-6, userA.initialRemainingEtaSeconds / 60);
    const leadMinutes = Math.max(0, Number(targetLeadDeltaMin) || 0);
    return Math.max(0.03, Math.min(0.95, leadMinutes / aEtaMinutes));
  }

  return Math.max(0, Math.min(1, Number(progress) || 0));
}

async function makeCandidate({
  id,
  group,
  scenarioLabel,
  expectedMatch,
  progress,
  targetLeadDeltaMin,
  targetDistanceKm,
  targetRoute,
  targetTime,
  targetSpatial,
  routePlan,
  useBaseRoute = false,
}) {
  let roadResult;

  if (useBaseRoute) {
    // user1〜3だけは「Car Aと同じ経路」を再現するため、
    // Google Mapsから取得済みのCar A実道路経路そのものを使用する。
    roadResult = {
      route: route.map(point => ({ ...point })),
      distanceMeters: baseCum[baseCum.length - 1] || 0,
      durationSeconds: routeDurationSeconds,
    };
  } else {
    const routeDefinition = {
      id,
      routePlan,
    };

    roadResult = await requestCandidateRoadRouteRobust(routeDefinition);
  }

  const candidateRoute = roadResult.route;
  const candidateCum = cumulativeDistances(candidateRoute);
  const initialProgress = resolveCandidateInitialProgress({
    progress,
    useBaseRoute,
    targetLeadDeltaMin,
  });
  const initialIndex = indexAtFraction(candidateCum, initialProgress);

  /*
   * 表のΔETAは「設計目標」。
   * Bが先行（+）ならAより残りETAを短く、
   * Bが後続（-）なら長くする。
   *
   * 実際の共通CPに対するΔETA / Time / Spatial / Scoreは
   * evaluate() が車両位置と経路から逐次再計算する。
   */
  const initialRemainingEtaSeconds = useBaseRoute
    ? Math.max(
        120,
        userA.initialRemainingEtaSeconds * (1 - initialProgress)
      )
    : Math.max(
        120,
        userA.initialRemainingEtaSeconds
          - Number(targetLeadDeltaMin || 0) * 60
      );

  return {
    id,
    group,
    scenarioLabel,
    expectedMatch,
    route: candidateRoute,
    initialProgress,
    initialIndex,
    currentIndex: initialIndex,
    initialRemainingEtaSeconds,
    actualRouteDistanceMeters: roadResult.distanceMeters,
    actualRouteDurationSeconds: roadResult.durationSeconds,
    routeGenerationStrategy: roadResult.generationStrategy || 'base-route',
    routeGenerationAttempt: roadResult.generationAttempt || 1,
    targetMetrics: {
      leadDeltaMin: targetLeadDeltaMin,
      distanceKm: targetDistanceKm,
      route: targetRoute,
      time: targetTime,
      spatial: targetSpatial,
    },
  };
}

function A(fraction) {
  return { kind: 'a', fraction };
}

function C(fraction, distanceKm, heading) {
  return { kind: 'cardinal', fraction, distanceKm, heading };
}

function N(fraction, distanceKm, side) {
  return { kind: 'normal', fraction, distanceKm, side };
}

async function buildCandidates() {
  states.clear();

  /*
   * 30台の経路パターン。
   *
   * 重要：user1〜3以外はCar Aの経路座標列をコピーして作らない。
   * 各車両ごとに、Car A周辺の相対地点と必要最小限のA上の接触点を
   * routePlanとして定義し、Google Maps Directions APIから独立した
   * 実道路経路を取得する。
   *
   * routePlanの記号：
   * A(f)          = Car A経路上のf地点
   * C(f, km, deg) = f地点から方位degへkm離れた地点
   * N(f, km, ±1)  = A経路の進行方向に対して左右へkm離れた地点
   *
   * targetRoute はあくまで設計目標で、実際のSimRouteは
   * matching.js内の1.1kmグリッドOverlap係数から動的計算する。
   */
  const definitions = [
    // 1〜3：Car Aと同じ経路を走る先行車
    {
      id:'user1', group:'leading_same_route',
      scenarioLabel:'Car Aと同じ経路を走る先行車', expectedMatch:true,
      progress:0, targetLeadDeltaMin:3, targetDistanceKm:2,
      targetRoute:1.00, targetTime:.811, targetSpatial:.869,
      useBaseRoute:true,
    },
    {
      id:'user2', group:'leading_same_route',
      scenarioLabel:'Car Aと同じ経路を走る先行車', expectedMatch:true,
      progress:0, targetLeadDeltaMin:6, targetDistanceKm:5,
      targetRoute:1.00, targetTime:.657, targetSpatial:.705,
      useBaseRoute:true,
    },
    {
      id:'user3', group:'leading_same_route',
      scenarioLabel:'Car Aと同じ経路を走る大きく先行した車', expectedMatch:true,
      progress:0, targetLeadDeltaMin:10, targetDistanceKm:8,
      targetRoute:.95, targetTime:.497, targetSpatial:.571,
      useBaseRoute:true,
    },

    // 4〜7：東西南北からCar Aへ合流
    {
      id:'user4', group:'merge_early',
      scenarioLabel:'北方面からCar Aへ合流', expectedMatch:true,
      progress:0, targetLeadDeltaMin:2, targetDistanceKm:2,
      targetRoute:.85, targetTime:.869, targetSpatial:.869,
      routePlan:[C(.12,7,0), A(.18), A(.55), A(1)],
    },
    {
      id:'user5', group:'merge_early',
      scenarioLabel:'南方面からCar Aへ合流', expectedMatch:true,
      progress:0, targetLeadDeltaMin:4, targetDistanceKm:3,
      targetRoute:.80, targetTime:.756, targetSpatial:.811,
      routePlan:[C(.15,7,180), A(.22), A(.60), A(1)],
    },
    {
      id:'user6', group:'merge_midway',
      scenarioLabel:'西方面からCar Aへ合流', expectedMatch:true,
      progress:0, targetLeadDeltaMin:5, targetDistanceKm:4,
      targetRoute:.65, targetTime:.705, targetSpatial:.756,
      routePlan:[C(.27,8,270), A(.38), A(.67), A(1)],
    },
    {
      id:'user7', group:'merge_midway',
      scenarioLabel:'東方面からCar Aへ合流', expectedMatch:true,
      progress:0, targetLeadDeltaMin:3, targetDistanceKm:3,
      targetRoute:.60, targetTime:.811, targetSpatial:.811,
      routePlan:[C(.30,8,90), A(.42), A(.70), A(1)],
    },

    // 8〜10：後半・GOAL付近で合流
    {
      id:'user8', group:'merge_late',
      scenarioLabel:'大きく迂回し経路後半でCar Aへ合流', expectedMatch:true,
      progress:0, targetLeadDeltaMin:7, targetDistanceKm:6,
      targetRoute:.40, targetTime:.613, targetSpatial:.657,
      routePlan:[C(.35,11,315), C(.50,8,270), A(.62), A(.84), A(1)],
    },
    {
      id:'user9', group:'merge_very_late',
      scenarioLabel:'別方向から終盤でCar Aへ合流', expectedMatch:true,
      progress:0, targetLeadDeltaMin:2, targetDistanceKm:2,
      targetRoute:.25, targetTime:.869, targetSpatial:.869,
      routePlan:[C(.48,10,135), C(.63,7,90), A(.77), A(1)],
    },
    {
      id:'user10', group:'goal_only',
      scenarioLabel:'別方向からGOAL付近でのみ合流', expectedMatch:false,
      progress:0, targetLeadDeltaMin:5, targetDistanceKm:5,
      targetRoute:.15, targetTime:.705, targetSpatial:.705,
      routePlan:[C(.60,12,225), C(.78,7,180), A(.91), A(1)],
    },

    // 11〜13：一部共有後に離脱
    {
      id:'user11', group:'leave_midway',
      scenarioLabel:'序盤を共有した後、北方面へ離脱', expectedMatch:true,
      progress:.06, targetLeadDeltaMin:1, targetDistanceKm:1,
      targetRoute:.35, targetTime:.932, targetSpatial:.932,
      routePlan:[A(0), A(.18), A(.36), C(.50,7,0), C(.70,10,20)],
    },
    {
      id:'user12', group:'leave_midway',
      scenarioLabel:'前半を共有した後、南方面へ離脱', expectedMatch:true,
      progress:.08, targetLeadDeltaMin:4, targetDistanceKm:4,
      targetRoute:.50, targetTime:.756, targetSpatial:.756,
      routePlan:[A(0), A(.24), A(.50), C(.64,7,180), C(.82,10,165)],
    },
    {
      id:'user13', group:'leave_late',
      scenarioLabel:'長く共有した後、終盤で別目的地へ離脱', expectedMatch:true,
      progress:.12, targetLeadDeltaMin:6, targetDistanceKm:5,
      targetRoute:.75, targetTime:.657, targetSpatial:.705,
      routePlan:[A(0), A(.35), A(.70), C(.82,6,60), C(.95,9,45)],
    },

    // 14〜20：短区間・中間区間・複数区間だけ共有
    {
      id:'user14', group:'short_shared',
      scenarioLabel:'ごく短い区間だけCar Aと共有', expectedMatch:false,
      progress:0, targetLeadDeltaMin:2, targetDistanceKm:3,
      targetRoute:.20, targetTime:.869, targetSpatial:.811,
      routePlan:[C(.20,8,225), A(.35), A(.43), C(.55,8,45), C(.72,10,60)],
    },
    {
      id:'user15', group:'middle_only',
      scenarioLabel:'中間区間だけCar Aと共有', expectedMatch:false,
      progress:0, targetLeadDeltaMin:8, targetDistanceKm:7,
      targetRoute:.45, targetTime:.571, targetSpatial:.613,
      routePlan:[C(.18,9,315), A(.34), A(.64), C(.78,9,135), C(.90,11,150)],
    },
    {
      id:'user16', group:'middle_only',
      scenarioLabel:'北西から接近し中盤だけ共有して北東へ離脱', expectedMatch:true,
      progress:0, targetLeadDeltaMin:3, targetDistanceKm:2,
      targetRoute:.40, targetTime:.811, targetSpatial:.869,
      routePlan:[C(.18,10,315), A(.38), A(.56), C(.69,8,45), C(.85,11,30)],
    },
    {
      id:'user17', group:'middle_long',
      scenarioLabel:'南西から接近し長めの中盤区間を共有して南東へ離脱', expectedMatch:true,
      progress:0, targetLeadDeltaMin:5, targetDistanceKm:4,
      targetRoute:.55, targetTime:.705, targetSpatial:.756,
      routePlan:[C(.12,10,225), A(.28), A(.66), C(.78,8,135), C(.92,11,150)],
    },
    {
      id:'user18', group:'middle_short',
      scenarioLabel:'別道路から一瞬だけCar Aと共有して再び離脱', expectedMatch:false,
      progress:0, targetLeadDeltaMin:1, targetDistanceKm:1,
      targetRoute:.15, targetTime:.932, targetSpatial:.932,
      routePlan:[N(.30,5,-1), A(.48), A(.52), N(.68,5,1), N(.84,7,1)],
    },
    {
      id:'user19', group:'multi_shared',
      scenarioLabel:'2か所だけ部分的にCar Aと経路共有', expectedMatch:false,
      progress:0, targetLeadDeltaMin:7, targetDistanceKm:8,
      targetRoute:.35, targetTime:.613, targetSpatial:.571,
      routePlan:[
        N(.18,6,-1), A(.30), A(.39), N(.52,6,1),
        A(.67), A(.75), N(.88,7,-1)
      ],
    },
    {
      id:'user20', group:'multi_shared',
      scenarioLabel:'3か所で断続的にCar Aと経路共有', expectedMatch:true,
      progress:0, targetLeadDeltaMin:2, targetDistanceKm:2,
      targetRoute:.50, targetTime:.869, targetSpatial:.869,
      routePlan:[
        N(.15,6,1), A(.26), A(.34), N(.42,5,-1),
        A(.50), A(.58), N(.64,5,1), A(.72), A(.80), N(.90,7,-1)
      ],
    },

    // 21〜22：遠方の別経路から合流
    {
      id:'user21', group:'merge_very_late',
      scenarioLabel:'遠方の別経路から終盤でCar A付近へ合流', expectedMatch:false,
      progress:0, targetLeadDeltaMin:12, targetDistanceKm:10,
      targetRoute:.30, targetTime:.432, targetSpatial:.497,
      routePlan:[C(.18,16,225), C(.42,12,270), A(.72), A(.88), A(1)],
    },
    {
      id:'user22', group:'merge_midway',
      scenarioLabel:'遠方の別経路から中盤以降にCar Aへ合流', expectedMatch:true,
      progress:0, targetLeadDeltaMin:4, targetDistanceKm:6,
      targetRoute:.60, targetTime:.756, targetSpatial:.657,
      routePlan:[C(.12,16,45), C(.28,11,90), A(.43), A(.72), A(1)],
    },

    // 23〜24：Car A近くの並行道路
    {
      id:'user23', group:'parallel',
      scenarioLabel:'Car A近くの並行道路を走行', expectedMatch:false,
      progress:0, targetLeadDeltaMin:1, targetDistanceKm:1,
      targetRoute:.10, targetTime:.932, targetSpatial:.932,
      routePlan:[N(.12,1.8,1), N(.38,1.8,1), N(.64,1.8,1), N(.88,1.8,1)],
    },
    {
      id:'user24', group:'parallel',
      scenarioLabel:'Car Aと反対側の並行道路を長距離走行', expectedMatch:false,
      progress:0, targetLeadDeltaMin:3, targetDistanceKm:2,
      targetRoute:.05, targetTime:.811, targetSpatial:.869,
      routePlan:[N(.08,2.6,-1), N(.34,2.6,-1), N(.62,2.6,-1), N(.92,2.6,-1)],
    },

    // 25：遠方から接近し後半を比較的長く共有
    {
      id:'user25', group:'high_overlap_far_cp',
      scenarioLabel:'遠方から接近し後半の経路を比較的長く共有', expectedMatch:true,
      progress:0, targetLeadDeltaMin:5, targetDistanceKm:10,
      targetRoute:.70, targetTime:.705, targetSpatial:.497,
      routePlan:[C(.08,15,315), C(.20,10,270), A(.35), A(.68), A(1)],
    },

    // 26〜27：1回または複数回交差
    {
      id:'user26', group:'crossing',
      scenarioLabel:'Car Aの経路と1回だけ交差', expectedMatch:false,
      progress:0, targetLeadDeltaMin:2, targetDistanceKm:1,
      targetRoute:.05, targetTime:.869, targetSpatial:.932,
      routePlan:[N(.38,7,-1), A(.56), N(.72,7,1)],
    },
    {
      id:'user27', group:'crossing',
      scenarioLabel:'Car Aの経路と複数回交差', expectedMatch:false,
      progress:0, targetLeadDeltaMin:6, targetDistanceKm:3,
      targetRoute:.10, targetTime:.657, targetSpatial:.811,
      routePlan:[N(.18,7,-1), A(.34), N(.48,7,1), A(.62), N(.78,7,-1), A(.86), N(.94,7,1)],
    },

    // 28：異なる方向から同じ目的地へ
    {
      id:'user28', group:'goal_only',
      scenarioLabel:'異なる方向からCar Aと同じ目的地へ向かう', expectedMatch:true,
      progress:0, targetLeadDeltaMin:1, targetDistanceKm:.5,
      targetRoute:.20, targetTime:.932, targetSpatial:.966,
      routePlan:[C(.52,13,135), C(.72,8,90), A(1)],
    },

    // 29〜30：異なる目的地・地域を走る無関係車
    {
      id:'user29', group:'unrelated',
      scenarioLabel:'Car Aの近くを走るが異なる目的地へ向かう無関係車', expectedMatch:false,
      progress:0, targetLeadDeltaMin:4, targetDistanceKm:5,
      targetRoute:.05, targetTime:.756, targetSpatial:.705,
      routePlan:[N(.22,4.5,1), N(.48,5.5,1), C(.72,9,35)],
    },
    {
      id:'user30', group:'unrelated',
      scenarioLabel:'Car Aとは異なる地域・目的地を走る無関係車', expectedMatch:false,
      progress:0, targetLeadDeltaMin:.5, targetDistanceKm:.5,
      targetRoute:.00, targetTime:.966, targetSpatial:.966,
      routePlan:[C(.12,18,45), C(.45,20,55), C(.78,22,65)],
    },
  ];

  const failedDefinitions = [];

  // Directions APIへの瞬間的な集中を避けるため3台ずつ生成する。
  for (let start = 0; start < definitions.length; start += CANDIDATE_BATCH_SIZE) {
    const batch = definitions.slice(start, start + CANDIDATE_BATCH_SIZE);
    setStatus(
      `候補車の実道路経路を取得中… ${states.size} / ${CANDIDATE_TARGET_COUNT}台生成済み`
    );

    const settled = await Promise.allSettled(batch.map(makeCandidate));

    settled.forEach((result, index) => {
      if (result.status === 'rejected') {
        console.warn(batch[index].id, result.reason);
        failedDefinitions.push(batch[index]);
        return;
      }

      const candidate = result.value;
      states.set(candidate.id, {
        candidate,
        cum: cumulativeDistances(candidate.route),
      });
    });

    if (start + CANDIDATE_BATCH_SIZE < definitions.length) {
      await sleep(CANDIDATE_BATCH_DELAY_MS);
    }
  }

  // バッチ処理で失敗した車両だけを1台ずつ最終再試行する。
  // 同時リクエストをなくすことでOVER_QUERY_LIMIT等の一時失敗を回避する。
  for (const definition of failedDefinitions) {
    if (states.has(definition.id)) continue;

    setStatus(
      `${definition.id} を再取得中… ${states.size} / ${CANDIDATE_TARGET_COUNT}台生成済み`
    );

    await sleep(CANDIDATE_RETRY_BASE_DELAY_MS * 2);

    try {
      const candidate = await makeCandidate(definition);
      states.set(candidate.id, {
        candidate,
        cum: cumulativeDistances(candidate.route),
      });
    } catch (error) {
      console.error(`${definition.id}: 最終再取得にも失敗`, error);
    }
  }

  const missingIds = definitions
    .map(definition => definition.id)
    .filter(id => !states.has(id));

  // 研究用データでは28/30台等の不完全な状態を許可しない。
  // 30台そろった場合だけシミュレーション開始を許可する。
  if (states.size !== CANDIDATE_TARGET_COUNT || missingIds.length) {
    states.clear();
    throw new Error(
      `候補車両を30台生成できませんでした`
      + `（${CANDIDATE_TARGET_COUNT - missingIds.length}/${CANDIDATE_TARGET_COUNT}台）`
      + `。未生成: ${missingIds.join(', ')}`
      + `。通信状態を確認して再度「Google Maps経路を生成」を実行してください。`
    );
  }

  setStatus(`候補車両 ${states.size} / ${CANDIDATE_TARGET_COUNT}台の実道路経路を取得しました．`);
}

function clearSimulationVisuals() {
  if (aMarker) {
    aMarker.setMap(null);
  }

  if (originMarker) {
    originMarker.setMap(null);
  }

  if (destinationMarker) {
    destinationMarker.setMap(null);
  }

  aMarker = null;
  originMarker = null;
  destinationMarker = null;

  cpMarkers.forEach(
    marker =>
      marker.setMap(null)
  );

  cpMarkers = [];

  candidateMarkers.forEach(
    marker =>
      marker.setMap(null)
  );

  candidateMarkers.clear();

  candidateLines.forEach(
    line =>
      line.setMap(null)
  );

  candidateLines.clear();

  commonCpHighlights.forEach(
    marker =>
      marker.setMap(null)
  );

  commonCpHighlights.clear();
}

async function generateExperiment() {
  if (generationInProgress) return;
  generationInProgress = true;
  el.generate.disabled = true;
  stop();
  el.start.disabled = true;
  el.pause.disabled = true;
  el.reset.disabled = true;
  experimentMeta = null;
  clearTimeSeriesLog();
  clearSimulationVisuals();

  directionsRenderer.set(
    'directions',
    null
  );

  setStatus(
    'Google Mapsで経路を取得しています…'
  );

  try {
    const result =
      await requestGoogleRoute();

    directionsRenderer
      .setDirections(
        result
      );

    const googleRoute =
      result.routes[0];

    const leg =
      googleRoute.legs[0];

    route =
      sampleRoute(
        googleRoute.overview_path,
        40
      );

    baseCum =
      cumulativeDistances(
        route
      );

    const actualDistanceMeters =
      Number(
        leg.distance?.value
      )
      ||
      baseCum[
        baseCum.length - 1
      ];

    routeDurationSeconds =
      Number(
        leg.duration?.value
      )
      || 1;

    const cpResult =
      buildDistanceBasedCheckpoints(
        route,
        baseCum
      );

    // 走行距離に応じて生成された中間チェックポイント
    const intermediateCheckpoints =
      cpResult.checkpoints;

    // 最後の中間チェックポイント通過後もマッチングを継続するため，
    // 目的地を終端評価地点 GOAL として追加する．
    const goalCheckpoint = {
      id: 'GOAL',
      name: '目的地',
      fraction: 1.0,
      routeIndex: route.length - 1,
      location: route[route.length - 1],
      isDestination: true,
    };

    checkpoints = [
      ...intermediateCheckpoints,
      goalCheckpoint,
    ];

    divisions =
      cpResult.divisions;

    const initialAIndex =
      indexAtFraction(
        baseCum,
        CAR_A_INITIAL_PROGRESS
      );

    const remainingDistanceRatio =
      (
        baseCum[
          baseCum.length - 1
        ]
        -
        baseCum[
          initialAIndex
        ]
      )
      /
      baseCum[
        baseCum.length - 1
      ];

    userA = {
      initialIndex:
        initialAIndex,

      initialRemainingEtaSeconds:
        Math.max(
          60,
          routeDurationSeconds
          * remainingDistanceRatio
        ),
    };

    elapsed = 0;

    await buildCandidates();

    experimentMeta = {
      origin: leg.start_address || el.originInput.value.trim(),
      destination: leg.end_address || el.destinationInput.value.trim(),
      routeDistanceKm: actualDistanceMeters / 1000,
      divisions,
      candidateCount: states.size,
      initialAProgressPct: CAR_A_INITIAL_PROGRESS * 100,
    };

    drawExperimentMap(
      leg
    );

    renderCheckpoints();

    update();

    el.origin.textContent =
      leg.start_address
      ||
      el.originInput.value.trim();

    el.destination.textContent =
      leg.end_address
      ||
      el.destinationInput.value.trim();

    el.routeDistance.textContent =
      `${
        (
          actualDistanceMeters
          / 1000
        ).toFixed(2)
      } km`;

    el.divisionCount.textContent =
      `${divisions}分割`;

    const intermediateCheckpointCount =
      checkpoints.filter(
        cp => !cp.isDestination
      ).length;

    el.checkpointCount.textContent =
      `${intermediateCheckpointCount}地点`;

    el.start.disabled = false;
    el.pause.disabled = true;
    el.reset.disabled = false;

    setStatus(
      `経路生成完了．候補車両 ${states.size} / ${CANDIDATE_TARGET_COUNT}台．`
      + `${(actualDistanceMeters / 1000).toFixed(2)} km`
      + ` → ${divisions}分割`
      + ` → 中間チェックポイント ${intermediateCheckpointCount}地点．`
    );

  } catch (error) {
    console.error(error);
    el.start.disabled = true;
    el.pause.disabled = true;
    el.reset.disabled = true;

    setStatus(
      `経路生成失敗: ${error.message}`,
      true
    );
  } finally {
    generationInProgress = false;
    el.generate.disabled = false;
  }
}

function drawExperimentMap(
  leg
) {
  originMarker =
    new google.maps.Marker({
      position:
        latLngObject(
          leg.start_location
        ),

      map,

      title:
        '出発地',

      label: {
        text:'S',
        color:'#fff',
      },

      icon:
        markerIcon(
          '#2563eb',
          9
        ),

      zIndex:
        100,
    });

  destinationMarker =
    new google.maps.Marker({
      position:
        latLngObject(
          leg.end_location
        ),

      map,

      title:
        '目的地',

      label: {
        text:'G',
        color:'#fff',
      },

      icon:
        markerIcon(
          '#dc2626',
          9
        ),

      zIndex:
        100,
    });

  cpMarkers =
    checkpoints
      .filter(cp => !cp.isDestination)
      .map(
      (cp, index) =>
        new google.maps.Marker({
          position:
            cp.location,

          map,

          title:
            `${cp.id}：`
            + `走行距離 `
            + `${(cp.fraction * 100).toFixed(1)}%地点`,

          label: {
            text:
              `CP${index + 1}`,

            color:
              '#f59e0b',

            fontSize:
              '13px',

            fontWeight:
              '700',
          },

          icon: {
            ...markerIcon(
              '#f59e0b',
              7
            ),

            labelOrigin:
              new google.maps.Point(
                0,
                -9
              ),
          },

          zIndex:
            70,
        })
    );

  for (
    const state
    of states.values()
  ) {
    const candidate =
      state.candidate;
candidateLines.set(
      candidate.id,

      new google.maps.Polyline({
        path:
          candidate.route,

        map,

        strokeColor: '#64748b',
        strokeOpacity: 0.20,

        strokeWeight:
          3,

        zIndex:
          10,
      })
    );
  }
}

function indexAtElapsedByDistance({
  cumulative,
  initialIndex,
  remainingEtaSeconds,
  timeSeconds,
}) {
  if (!Array.isArray(cumulative) || !cumulative.length) {
    return 0;
  }

  const lastIndex = cumulative.length - 1;
  const startIndex = Math.max(
    0,
    Math.min(lastIndex, Number(initialIndex) || 0)
  );
  const fraction = Math.min(
    1,
    Math.max(0, Number(timeSeconds) || 0)
      / Math.max(1, Number(remainingEtaSeconds) || 1)
  );

  // 配列indexではなく累積走行距離を基準に移動させる。
  // これにより、経路サンプリング点の密度に左右されず、
  // 「経過時間の割合 = 残り走行距離の進捗割合」となる。
  const startDistance = cumulative[startIndex] || 0;
  const endDistance = cumulative[lastIndex] || startDistance;
  const targetDistance = startDistance
    + fraction * Math.max(0, endDistance - startDistance);

  if (endDistance <= 0) {
    return startIndex;
  }

  // 目的地だけは実際の残り時間を消化した時点で到達扱いにする。
  // 最近傍indexを使うと，最終サンプリング点へ最大約半間隔だけ早く到達し，
  // 10秒ログと最終ログの双方に100%到達行が記録される場合がある。
  if (fraction >= 1) {
    return lastIndex;
  }

  // targetDistanceを超えない最後の経路点を採用する。
  // 経路は約40m間隔でサンプリングされているため，位置誤差は最大1区間程度。
  let low = startIndex;
  let high = lastIndex;
  let best = startIndex;

  while (low <= high) {
    const mid = Math.floor((low + high) / 2);
    if ((cumulative[mid] || 0) <= targetDistance) {
      best = mid;
      low = mid + 1;
    } else {
      high = mid - 1;
    }
  }

  return best;
}

function aIndexAtElapsed(timeSeconds) {
  if (!userA) {
    return 0;
  }

  return indexAtElapsedByDistance({
    cumulative: baseCum,
    initialIndex: userA.initialIndex,
    remainingEtaSeconds: userA.initialRemainingEtaSeconds,
    timeSeconds,
  });
}

function candidateIndexAtElapsed(
  candidate,
  candidateCum,
  timeSeconds
) {
  return indexAtElapsedByDistance({
    cumulative: candidateCum,
    initialIndex: candidate.initialIndex,
    remainingEtaSeconds: candidate.initialRemainingEtaSeconds,
    timeSeconds,
  });
}

function currentAIndex() {
  return aIndexAtElapsed(elapsed);
}

function updateMarkers(
  ai
) {
  const pointA =
    route[ai];

  if (!aMarker) {
    aMarker =
      new google.maps.Marker({
        position:
          pointA,

        map,

        title:
          'Car A',

        label: {
          text:'A',
          color:'#fff',
          fontSize:'10px',
        },

        icon:
          markerIcon(
            '#00a8ff',
            10
          ),

        zIndex:
          120,
      });
  } else {
    aMarker.setPosition(
      pointA
    );
  }

  for (
    const state
    of states.values()
  ) {
    const c =
      state.candidate;

    c.currentIndex = candidateIndexAtElapsed(
      c,
      state.cum,
      elapsed
    );

    const point =
      c.route[
        c.currentIndex
      ];

    let marker =
      candidateMarkers.get(
        c.id
      );

    if (!marker) {
      marker =
        new google.maps.Marker({
          position:
            point,

          map,

          title:
            `${c.id} / ${c.scenarioLabel || typeNames[c.group] || c.group}`,

          label: {
            text:
              c.id.replace(
                'user',
                ''
              ),

            color:
              '#fff',

            fontSize:
              '9px',
          },

          icon:
            markerIcon('#64748b', 7),

          zIndex:
            90,
        });

      marker.addListener(
        'click',
        () =>
          renderDetail(
            c.id
          )
      );

      candidateMarkers.set(
        c.id,
        marker
      );

    } else {
      marker.setPosition(
        point
      );
    }
  }
}

function evaluateAll(
  ai
) {
  const results = [];

  for (
    const state
    of states.values()
  ) {
    const c =
      state.candidate;

    results.push({
      id:
        c.id,

      candidate:
        c,

      result:
        evaluate({
          userA,
          candidate:
            c,

          checkpoints,

          currentAIndex:
            ai,

          currentBIndex:
            c.currentIndex,

          elapsedSeconds:
            elapsed,

          baseCum,

          baseRoute:
            route,

          candidateCum:
            state.cum,
        }),
    });
  }

  return results.sort(
    (a, b) => {
      // MATCH判定を優先し，同じ判定内ではScoreの高い順に並べる．
      if (a.result.eligible !== b.result.eligible) {
        return a.result.eligible ? -1 : 1;
      }

      return b.result.score - a.result.score;
    }
  );
}

function evaluateAllAtTime(snapshotElapsed) {
  const ai = aIndexAtElapsed(snapshotElapsed);
  const results = [];

  for (const state of states.values()) {
    const c = state.candidate;
    const bi = candidateIndexAtElapsed(
      c,
      state.cum,
      snapshotElapsed
    );

    results.push({
      id: c.id,
      candidate: c,
      result: evaluate({
        userA,
        candidate: c,
        checkpoints,
        currentAIndex: ai,
        currentBIndex: bi,
        elapsedSeconds: snapshotElapsed,
        baseCum,
        baseRoute: route,
        candidateCum: state.cum,
      }),
    });
  }

  results.sort((a, b) => {
    if (a.result.eligible !== b.result.eligible) {
      return a.result.eligible ? -1 : 1;
    }
    return b.result.score - a.result.score;
  });

  return { ai, results };
}

function roundedNumber(value, digits = 6) {
  return Number.isFinite(value)
    ? Number(value.toFixed(digits))
    : '';
}

function renderLogStatus() {
  if (el.logSnapshotCount) {
    el.logSnapshotCount.textContent = `${loggedSnapshotTimes.size} 時点`;
  }

  if (el.logRowCount) {
    el.logRowCount.textContent = `${simulationLog.length} 行`;
  }

  if (el.exportCsv) {
    el.exportCsv.disabled = simulationLog.length === 0;
  }
}

function clearTimeSeriesLog() {
  simulationLog = [];
  nextLogElapsed = 0;
  loggedSnapshotTimes = new Set();
  renderLogStatus();
}

function appendTimeSeriesSnapshot(snapshotElapsed) {
  if (!userA || !states.size) return;

  const timeSec = Math.max(0, Number(snapshotElapsed) || 0);
  const timeKey = timeSec.toFixed(3);
  if (loggedSnapshotTimes.has(timeKey)) return;

  const { ai, results } = evaluateAllAtTime(timeSec);
  const matches = results.filter(item => item.result.eligible);
  const topMatch = matches[0] || null;
  const matchRank = new Map(
    matches.map((item, index) => [item.id, index + 1])
  );

  const totalDistance = baseCum[baseCum.length - 1] || 1;
  const aProgressPct = (baseCum[ai] / totalDistance) * 100;

  results.forEach(item => {
    const r = item.result;
    simulationLog.push({
      experiment_origin: experimentMeta?.origin || '',
      experiment_destination: experimentMeta?.destination || '',
      route_distance_km: roundedNumber(experimentMeta?.routeDistanceKm),
      initial_a_progress_pct: roundedNumber(experimentMeta?.initialAProgressPct, 3),
      time_sec: roundedNumber(timeSec, 3),
      time_min: roundedNumber(timeSec / 60),
      a_progress_pct: roundedNumber(aProgressPct, 3),
      vehicle_id: item.id,
      scenario: item.candidate.scenarioLabel || typeNames[item.candidate.group] || item.candidate.group,
      common_cp: r.cp ? (r.cp.isDestination ? 'GOAL' : r.cp.id) : '',
      system_mode: r.systemMode || '',
      evaluation_mode: r.evaluationMode || '',
      candidate_initial_progress_pct: roundedNumber((item.candidate.initialProgress || 0) * 100, 3),
      candidate_route_distance_km: roundedNumber(item.candidate.actualRouteDistanceMeters / 1000, 6),
      route_generation_strategy: item.candidate.routeGenerationStrategy || '',
      route_generation_attempt: item.candidate.routeGenerationAttempt || 1,
      sim_route: roundedNumber(r.simRoute),
      sim_time: roundedNumber(r.simTime),
      sim_spatial: roundedNumber(r.simSpatial),
      score: roundedNumber(r.score),
      eta_a_min: roundedNumber(r.etaA),
      eta_b_min: roundedNumber(r.etaB),
      delta_eta_abs_min: roundedNumber(r.deltaEta),
      lead_delta_min: roundedNumber(r.leadDeltaMinutes),
      candidate_is_ahead: r.candidateIsAhead ? 1 : 0,
      distance_a_to_cp_km: roundedNumber(r.distanceKm),
      match: r.eligible ? 1 : 0,
      reason: r.reason || '',
      match_count: matches.length,
      match_rank: matchRank.get(item.id) || '',
      top_match_vehicle: topMatch?.id || '',
      top_match_score: roundedNumber(topMatch?.result?.score),
      common_grid_count: Number.isFinite(r.commonGridCount) ? r.commonGridCount : '',
      grid_count_a: Number.isFinite(r.gridCountA) ? r.gridCountA : '',
      grid_count_b: Number.isFinite(r.gridCountB) ? r.gridCountB : '',
    });
  });

  loggedSnapshotTimes.add(timeKey);
  renderLogStatus();
}

function recordPendingTimeSeriesSnapshots(upToElapsed) {
  if (!userA || !states.size) return;

  const maxElapsed = Math.min(
    Math.max(0, Number(upToElapsed) || 0),
    userA.initialRemainingEtaSeconds
  );

  while (nextLogElapsed <= maxElapsed + 1e-9) {
    appendTimeSeriesSnapshot(nextLogElapsed);
    nextLogElapsed += LOG_INTERVAL_SIM_SEC;
  }
}

function csvEscape(value) {
  const text = value == null ? '' : String(value);
  return /[",\n\r]/.test(text)
    ? `"${text.replace(/"/g, '""')}"`
    : text;
}

function exportTimeSeriesCsv() {
  if (!simulationLog.length) {
    setStatus('出力できる時系列ログがありません．', true);
    return;
  }

  const columns = [
    'experiment_origin',
    'experiment_destination',
    'route_distance_km',
    'initial_a_progress_pct',
    'time_sec',
    'time_min',
    'a_progress_pct',
    'vehicle_id',
    'scenario',
    'common_cp',
    'system_mode',
    'evaluation_mode',
    'candidate_initial_progress_pct',
    'candidate_route_distance_km',
    'route_generation_strategy',
    'route_generation_attempt',
    'sim_route',
    'sim_time',
    'sim_spatial',
    'score',
    'eta_a_min',
    'eta_b_min',
    'delta_eta_abs_min',
    'lead_delta_min',
    'candidate_is_ahead',
    'distance_a_to_cp_km',
    'match',
    'reason',
    'match_count',
    'match_rank',
    'top_match_vehicle',
    'top_match_score',
    'common_grid_count',
    'grid_count_a',
    'grid_count_b',
  ];

  const lines = [
    columns.join(','),
    ...simulationLog.map(row =>
      columns.map(column => csvEscape(row[column])).join(',')
    ),
  ];

  // Excel等でも日本語が文字化けしにくいようUTF-8 BOMを付与する．
  const blob = new Blob(
    [`\uFEFF${lines.join('\r\n')}`],
    { type: 'text/csv;charset=utf-8;' }
  );

  const now = new Date();
  const pad = value => String(value).padStart(2, '0');
  const filename =
    `driveria_timeseries_${now.getFullYear()}`
    + `${pad(now.getMonth() + 1)}${pad(now.getDate())}_`
    + `${pad(now.getHours())}${pad(now.getMinutes())}${pad(now.getSeconds())}.csv`;

  const url = URL.createObjectURL(blob);
  const anchor = document.createElement('a');
  anchor.href = url;
  anchor.download = filename;
  document.body.appendChild(anchor);
  anchor.click();
  anchor.remove();
  URL.revokeObjectURL(url);

  setStatus(
    `時系列ログをCSV出力しました．${loggedSnapshotTimes.size}時点 / ${simulationLog.length}行`
  );
}

function highlightCommonCheckpoints(
  results
) {
  commonCpHighlights.forEach(
    marker =>
      marker.setMap(null)
  );

  commonCpHighlights.clear();

  for (
    const item
    of results
  ) {
    const cp =
      item.result.cp;

    if (
      !cp
      ||
      commonCpHighlights.has(
        cp.id
      )
    ) {
      continue;
    }

    const marker =
      new google.maps.Marker({
        position:
          cp.location,

        map,

        title:
          `現在の評価対象共通チェックポイント：${cp.id}`,

        icon: {
          path:
            google.maps.SymbolPath.CIRCLE,

          scale:
            13,

          fillColor:
            '#f59e0b',

          fillOpacity:
            0.12,

          strokeColor:
            '#f59e0b',

          strokeWeight:
            3,
        },

        zIndex:
          75,
      });

    commonCpHighlights.set(
      cp.id,
      marker
    );
  }
}

function renderCheckpoints() {
  el.checkpointList.innerHTML =
    checkpoints
      .map(
        cp => `
          <div class="checkpoint-item ${cp.isDestination ? 'goal-item' : ''}">
            <strong>
              ${escapeHtml(cp.isDestination ? 'GOAL（目的地）' : cp.id)}
            </strong>

            <span>
              ${
                cp.isDestination
                  ? '最終評価地点'
                  : `${(cp.fraction * 100).toFixed(1)}%地点`
              }
            </span>

            <small>
              ${cp.location.lat.toFixed(6)},
              ${cp.location.lng.toFixed(6)}
            </small>
          </div>
        `
      )
      .join('');
}

function renderList(
  results
) {
  el.candidateList.innerHTML =
    results
      .map(
        item => {
          const r =
            item.result;
return `
            <button
              class="candidate-card ${r.eligible ? 'matched' : ''}"
              data-id="${item.id}"
              type="button"
            >
              <div class="head">
                <strong>${item.id}</strong>

                <span class="type">
                  ${item.candidate.scenarioLabel || typeNames[item.candidate.group] || item.candidate.group}
                </span>
              </div>

              <div class="main">
                <span>
                  ${r.eligible ? 'MATCH' : 'NO MATCH'}
                </span>

                <strong>
                  Score ${f3(r.score)}
                </strong>
              </div>

              <div class="cp">
                共通チェックポイント:
                ${r.cp ? (r.cp.isDestination ? 'GOAL（目的地）' : r.cp.id) : 'なし'}
                <br>
                先行条件:
                ${
                  r.leadDeltaMinutes == null
                    ? '—'
                    : r.candidateIsAhead
                      ? `○ Bが${Math.abs(r.leadDeltaMinutes).toFixed(2)}分先行`
                      : `× Bが${Math.abs(r.leadDeltaMinutes).toFixed(2)}分後続`
                }
              </div>

              <div class="mini">
                <span>
                  Route
                  <br>
                  <b>${f3(r.simRoute)}</b>
                </span>

                <span>
                  Time
                  <br>
                  <b>${f3(r.simTime)}</b>
                </span>

                <span>
                  Spatial
                  <br>
                  <b>${f3(r.simSpatial)}</b>
                </span>
              </div>
            </button>
          `;
        }
      )
      .join('');

  el.candidateList
    .querySelectorAll(
      '[data-id]'
    )
    .forEach(
      button => {
        button.addEventListener(
          'click',
          () => {
            const id =
              button.dataset.id;

            renderDetail(
              id,
              results
            );

            const state =
              states.get(id);

            if (state) {
              map.panTo(
                state.candidate.route[
                  state.candidate.currentIndex
                ]
              );
            }
          }
        );
      }
    );
}

function renderDetail(
  id,
  cached = null
) {
  if (!userA) {
    return;
  }

  const results =
    cached
    ||
    evaluateAll(
      currentAIndex()
    );

  const item =
    results.find(
      x =>
        x.id === id
    );

  if (!item) {
    return;
  }

  const r =
    item.result;

  el.vehicleDetail.innerHTML = `
    <div class="detail-title">
      ${item.id}

      <span>
        ${item.candidate.scenarioLabel || typeNames[item.candidate.group] || item.candidate.group}
      </span>
    </div>

    <div class="detail-grid">
      <div>
        <small>共通チェックポイント</small>
        <b>${r.cp ? (r.cp.isDestination ? 'GOAL（目的地）' : r.cp.id) : 'なし'}</b>
      </div>

      <div>
        <small>ETA A→チェックポイント</small>
        <b>${fm(r.etaA)}</b>
      </div>

      <div>
        <small>ETA B→チェックポイント</small>
        <b>${fm(r.etaB)}</b>
      </div>

      <div>
        <small>ΔETA（絶対値）</small>
        <b>${fm(r.deltaEta)}</b>
      </div>

      <div>
        <small>先行判定 ΔETA(A-B)</small>
        <b>
          ${
            r.leadDeltaMinutes == null
              ? '—'
              : `${r.leadDeltaMinutes.toFixed(2)} 分`
          }
        </b>
      </div>

      <div>
        <small>BはAより先か</small>
        <b>
          ${
            r.leadDeltaMinutes == null
              ? '—'
              : r.candidateIsAhead
                ? '○ 先行'
                : '× 後続'
          }
        </b>
      </div>

      <div>
        <small>A→チェックポイント距離</small>
        <b>${fk(r.distanceKm)}</b>
      </div>

      <div>
        <small>Route</small>
        <b>${f3(r.simRoute)}</b>
      </div>

      <div>
        <small>Time</small>
        <b>${f3(r.simTime)}</b>
      </div>

      <div>
        <small>Spatial</small>
        <b>${f3(r.simSpatial)}</b>
      </div>

      <div>
        <small>Score</small>
        <b>${f3(r.score)}</b>
      </div>

      <div>
        <small>候補車の実経路距離</small>
        <b>${fk(item.candidate.actualRouteDistanceMeters / 1000)}</b>
      </div>

      <div>
        <small>Overlap共通グリッド数</small>
        <b>${r.commonGridCount ?? '—'}</b>
      </div>

      <div>
        <small>Car Aグリッド数</small>
        <b>${r.gridCountA ?? '—'}</b>
      </div>

      <div>
        <small>候補車Bグリッド数</small>
        <b>${r.gridCountB ?? '—'}</b>
      </div>

      <div>
        <small>評価モード</small>
        <b>${
          r.evaluationMode === 'GOAL_MODE'
            ? 'GOALモード'
            : r.evaluationMode === 'NORMAL_MODE'
              ? '通常モード'
              : '—'
        }</b>
      </div>

      <div class="wide-detail">
        <small>使用重み</small>
        <b>${
          r.weights
            ? `Route ${r.weights.route.toFixed(2)} / Time ${r.weights.time.toFixed(2)} / Spatial ${r.weights.spatial.toFixed(2)}`
            : '—'
        }</b>
      </div>

      <div>
        <small>判定</small>
        <b>
          ${
            r.eligible
              ? 'MATCH'
              : 'NO MATCH'
          }
        </b>
      </div>
    </div>
  `;
}

function updateStats(
  ai,
  results
) {
  const point =
    route[ai];

  const progress =
    baseCum[ai]
    /
    baseCum[
      baseCum.length - 1
    ];

  const matches =
    results.filter(
      x =>
        x.result.eligible
    );

  el.simTime.textContent =
    `${(elapsed / 60).toFixed(2)} 分`;

  el.aProgress.textContent =
    `${(progress * 100).toFixed(1)} %`;

  el.aPosition.textContent =
    `${point.lat.toFixed(6)}, ${point.lng.toFixed(6)}`;

  el.matchCount.textContent =
    `${matches.length} / ${results.length}`;

  el.bestScore.textContent =
    matches.length
      ? matches[0].result.score.toFixed(3)
      : '—';

  if (el.systemMode) {
    const mode = results[0]?.result?.systemMode || '—';
    el.systemMode.textContent =
      mode === 'GOAL_MODE' ? 'GOALモード'
        : mode === 'NORMAL_MODE' ? '通常モード'
          : mode;
  }

  if (el.lastUpdate) {
    el.lastUpdate.textContent =
      `${(elapsed / 60).toFixed(2)} 分時点`;
  }
}

function update() {
  if (!userA) {
    return;
  }

  const ai =
    currentAIndex();

  updateMarkers(ai);

  const results =
    evaluateAll(ai);

  highlightCommonCheckpoints(
    results
  );

  renderList(
    results
  );

  updateStats(
    ai,
    results
  );

  recordPendingTimeSeriesSnapshots(elapsed);

  if (
    results.length
  ) {
    renderDetail(
      results[0].id,
      results
    );
  }

  if (
    ai
    >=
    route.length - 1
  ) {
    appendTimeSeriesSnapshot(elapsed);
    stop();

    setStatus(
      'Car A が目的地へ到着しました．'
    );
  }
}

function start() {
  if (
    !userA
    ||
    timer
  ) {
    return;
  }

  timer =
    setInterval(
      () => {
        const stepSeconds =
          BASE_STEP_SEC
          *
          (
            Number(
              el.speed.value
            )
            || 1
          );

        elapsed = Math.min(
          elapsed + stepSeconds,
          userA.initialRemainingEtaSeconds
        );

        update();
      },

      STEP_MS
    );

  el.start.disabled = true;
  el.pause.disabled = false;

  setStatus(
    'シミュレーション実行中'
  );
}

function stop() {
  clearInterval(timer);

  timer = null;

  if (userA) {
    el.start.disabled = false;
  }

  el.pause.disabled = true;
}

function reset() {
  stop();

  elapsed = 0;
  clearTimeSeriesLog();

  update();

  setStatus(
    '出発地点の初期状態へ戻しました．'
  );
}

function renderParameters() {
  el.parameterInfo.innerHTML = `
    <div><b>通常時</b> = 0.50 Route + 0.30 Time + 0.20 Spatial</div>
    <div><b>Route</b> = 将来経路を約1.1kmグリッド集合化したOverlap係数</div>
    <div><b>GOALモード</b> = Car Aが最終中間チェックポイントを通過した後のみ有効．0.60 Time + 0.40 Spatial（Routeは評価対象外）</div>
    <div><b>閾値</b> = ${CONFIG.threshold}</div>
    <div><b>Car A初期位置</b> = 出発地点（0%）</div>
    <div><b>分析ログ</b> = シミュレーション時間 ${LOG_INTERVAL_SIM_SEC} 秒間隔</div>
    <div>
      <b>MATCH必須条件</b>：
      ETA_A − ETA_B &gt; 0
      （候補車Bが共通チェックポイントへ先に到達）
    </div>
  `;
}


function applyTheme(theme) {
  const value = theme === 'light' ? 'light' : 'dark';
  document.documentElement.setAttribute('data-theme', value);
  localStorage.setItem('driveria-theme', value);

  if (el.themeToggle) {
    const light = value === 'light';
    el.themeToggle.textContent = light ? '☾' : '☀';
    el.themeToggle.title = light ? 'ダークモードへ切替' : 'ライトモードへ切替';
    el.themeToggle.setAttribute('aria-label', el.themeToggle.title);
  }
}

function toggleTheme() {
  const current =
    document.documentElement.getAttribute('data-theme') || 'dark';
  applyTheme(current === 'dark' ? 'light' : 'dark');
}

function initializeTheme() {
  const saved = localStorage.getItem('driveria-theme');
  if (saved === 'light' || saved === 'dark') {
    applyTheme(saved);
    return;
  }

  const light =
    window.matchMedia &&
    window.matchMedia('(prefers-color-scheme: light)').matches;

  applyTheme(light ? 'light' : 'dark');
}

function setPanelCollapsed(collapsed) {
  const value = Boolean(collapsed);

  document.body.classList.toggle(
    'panel-collapsed',
    value
  );

  localStorage.setItem(
    'driveria-panel-collapsed',
    value ? '1' : '0'
  );

  if (el.panelOpen) {
    el.panelOpen.classList.toggle(
      'visible',
      value
    );
  }

  // パネル開閉後にGoogle Mapsへコンテナサイズ変更を通知する
  if (typeof google !== 'undefined' && map) {
    window.setTimeout(() => {
      google.maps.event.trigger(map, 'resize');

      if (route.length) {
        const ai = currentAIndex();
        if (route[ai]) {
          map.setCenter(route[ai]);
        }
      }
    }, 80);

    window.setTimeout(() => {
      google.maps.event.trigger(map, 'resize');
    }, 320);
  }
}

function initializePanelState() {
  setPanelCollapsed(
    localStorage.getItem('driveria-panel-collapsed') === '1'
  );
}

async function main() {
  initializeTheme();
  initializePanelState();

  renderParameters();

  el.themeToggle?.addEventListener('click', toggleTheme);
  el.panelClose?.addEventListener('click', () => setPanelCollapsed(true));
  el.panelOpen?.addEventListener('click', () => setPanelCollapsed(false));

  el.generate.addEventListener(
    'click',
    generateExperiment
  );

  el.start.addEventListener(
    'click',
    start
  );

  el.pause.addEventListener(
    'click',
    stop
  );

  el.reset.addEventListener(
    'click',
    reset
  );

  el.exportCsv?.addEventListener(
    'click',
    exportTimeSeriesCsv
  );

  renderLogStatus();

  try {
    setStatus(
      'Google Mapsを読み込んでいます…'
    );

    await loadGoogleMaps();

    initMap();

    setStatus(
      '準備完了．出発地と目的地を入力して経路を生成してください．'
    );

  } catch (error) {
    console.error(error);

    setStatus(
      error.message,
      true
    );
  }
}

authElements.form?.addEventListener('submit', handleAuthSubmit);
