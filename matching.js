/**
 * Driveria common-checkpoint based matching model
 *
 * Time unit    : minute
 * Spatial unit : km
 * Route        : Overlap coefficient of future-route grid sets
 */

export const CONFIG = Object.freeze({
  kTime: 0.07,
  kSpatial: 0.07,
  threshold: 0.50,
  gridSizeMeters: 1100,

  normalWeights: Object.freeze({
    route: 0.50,
    time: 0.30,
    spatial: 0.20,
  }),

  goalWeights: Object.freeze({
    route: 0.00,
    time: 0.60,
    spatial: 0.40,
  }),
});

const EARTH_RADIUS_M = 6371000;
const METERS_PER_DEG_LAT = 111320;
const toRad = deg => deg * Math.PI / 180;

export function distanceMeters(a, b) {
  const lat1 = toRad(Number(a.lat));
  const lat2 = toRad(Number(b.lat));
  const dLat = lat2 - lat1;
  const dLng = toRad(Number(b.lng) - Number(a.lng));

  const h =
    Math.sin(dLat / 2) ** 2
    + Math.cos(lat1) * Math.cos(lat2) * Math.sin(dLng / 2) ** 2;

  return EARTH_RADIUS_M * 2
    * Math.atan2(Math.sqrt(h), Math.sqrt(1 - h));
}

export function cumulativeDistances(route) {
  const out = [0];

  for (let i = 1; i < route.length; i += 1) {
    out.push(
      out[i - 1]
      + distanceMeters(route[i - 1], route[i])
    );
  }

  return out;
}

export function routeDistance(cumulative, startIndex, endIndex) {
  const start = Math.max(0, Math.min(cumulative.length - 1, Number(startIndex)));
  const end = Math.max(0, Math.min(cumulative.length - 1, Number(endIndex)));
  if (end <= start) return 0;
  return cumulative[end] - cumulative[start];
}

export function indexAtFraction(cumulative, fraction) {
  const total = cumulative[cumulative.length - 1];
  const target = total * Math.max(0, Math.min(1, fraction));
  let bestIndex = 0;
  let bestDiff = Infinity;

  cumulative.forEach((value, index) => {
    const diff = Math.abs(value - target);
    if (diff < bestDiff) {
      bestDiff = diff;
      bestIndex = index;
    }
  });

  return bestIndex;
}

export function checkpointDivisionCount(distanceKm) {
  if (distanceKm < 10) return 3;
  if (distanceKm < 30) return 4;
  if (distanceKm <= 100) return 5;
  return 6;
}

export function buildDistanceBasedCheckpoints(route, cumulative) {
  const totalKm = cumulative[cumulative.length - 1] / 1000;
  const divisions = checkpointDivisionCount(totalKm);
  const checkpoints = [];

  for (let i = 1; i < divisions; i += 1) {
    const fraction = i / divisions;
    const routeIndex = indexAtFraction(cumulative, fraction);
    checkpoints.push({
      id: `チェックポイント${i}`,
      name: `チェックポイント${i}`,
      fraction,
      routeIndex,
      location: route[routeIndex],
    });
  }

  return { checkpoints, divisions };
}

export function computeSimTime(deltaEtaMinutes) {
  if (!Number.isFinite(deltaEtaMinutes)) return 0;
  return Math.exp(-CONFIG.kTime * Math.abs(deltaEtaMinutes));
}

export function computeSimSpatial(distanceKm) {
  if (!Number.isFinite(distanceKm)) return 0;
  return Math.exp(-CONFIG.kSpatial * Math.max(0, distanceKm));
}

export function computeScore(
  simRoute,
  simTime,
  simSpatial,
  weights = CONFIG.normalWeights
) {
  return (
    weights.route * simRoute
    + weights.time * simTime
    + weights.spatial * simSpatial
  );
}

/**
 * 緯度経度を約1.1 km四方のグリッドIDへ変換する。
 * 経度方向は緯度に応じてメートル換算する。
 */
export function gridKey(point, gridSizeMeters = CONFIG.gridSizeMeters) {
  const lat = Number(point.lat);
  const lng = Number(point.lng);
  const yMeters = lat * METERS_PER_DEG_LAT;
  const xMeters = lng * METERS_PER_DEG_LAT * Math.cos(toRad(lat));
  const gx = Math.floor(xMeters / gridSizeMeters);
  const gy = Math.floor(yMeters / gridSizeMeters);
  return `${gx}:${gy}`;
}

export function routeGridSet(route, startIndex = 0) {
  const set = new Set();
  if (!Array.isArray(route) || !route.length) return set;

  const start = Math.max(0, Math.min(route.length - 1, Number(startIndex) || 0));
  for (let i = start; i < route.length; i += 1) {
    set.add(gridKey(route[i]));
  }
  return set;
}

/** Overlap(A,B)=|A∩B| / min(|A|,|B|) */
export function overlapCoefficient(setA, setB) {
  if (!setA?.size || !setB?.size) return 0;
  const small = setA.size <= setB.size ? setA : setB;
  const large = small === setA ? setB : setA;
  let intersection = 0;
  small.forEach(key => {
    if (large.has(key)) intersection += 1;
  });
  return Math.max(0, Math.min(1, intersection / Math.min(setA.size, setB.size)));
}

/**
 * 現在位置以降の予定経路をグリッド集合化し、Overlap係数をSimRouteとする。
 * sharedRange等の人工的な割合は判定には使用しない。
 */
export function computeSimRouteByGrid({
  baseRoute,
  candidateRoute,
  currentAIndex,
  currentBIndex,
}) {
  const gridsA = routeGridSet(baseRoute, currentAIndex);
  const gridsB = routeGridSet(candidateRoute, currentBIndex);
  return overlapCoefficient(gridsA, gridsB);
}

function etaToIndexMinutes({
  cumulative,
  currentIndex,
  targetIndex,
  remainingEtaSeconds,
}) {
  if (targetIndex < currentIndex) return null;
  if (targetIndex === currentIndex) return 0;

  const remainingDistance = routeDistance(
    cumulative,
    currentIndex,
    cumulative.length - 1
  );
  const distanceToTarget = routeDistance(
    cumulative,
    currentIndex,
    targetIndex
  );

  if (remainingDistance <= 0) {
    return targetIndex === currentIndex ? 0 : null;
  }

  return (
    Math.max(0, remainingEtaSeconds)
    * (distanceToTarget / remainingDistance)
    / 60
  );
}

function candidateIndexForCheckpoint(candidate, checkpoint, currentBIndex) {
  if (!Array.isArray(candidate.route) || !candidate.route.length) return -1;
  const targetGrid = gridKey(checkpoint.location);
  const start = Math.max(
    0,
    Math.min(candidate.route.length - 1, Number(currentBIndex) || 0)
  );

  /*
   * 共通CPの成立判定自体は約1.1kmグリッドで行うが，ETAの到達地点には
   * 「そのグリッドへ最初に入った点」を使わない。
   * それを使うと，同一路線の車両でもCar AはCP座標，候補車Bはグリッド端
   * までのETAとなり，Bの先行時間が過大評価されるためである。
   *
   * 候補車Bの将来経路上でCPと同じグリッドに含まれる点のうち，
   * CP座標に最も近い点をETA算出地点として採用する。
   */
  let bestIndex = -1;
  let bestDistance = Infinity;

  for (let i = start; i < candidate.route.length; i += 1) {
    if (gridKey(candidate.route[i]) !== targetGrid) continue;

    const distance = distanceMeters(candidate.route[i], checkpoint.location);
    if (distance < bestDistance) {
      bestDistance = distance;
      bestIndex = i;
    }
  }

  return bestIndex;
}

function firstFutureCommonCheckpoint({
  checkpoints,
  candidate,
  currentAIndex,
  currentBIndex,
  allowDestination = false,
}) {
  const future = (checkpoints || [])
    .map(cp => {
      if (cp.isDestination && !allowDestination) return null;
      const cpIndex = Number(cp.routeIndex);
      if (cpIndex <= Number(currentAIndex)) return null;
      const candidateRouteIndex = candidateIndexForCheckpoint(
        candidate,
        cp,
        currentBIndex
      );
      return candidateRouteIndex >= 0
        ? { ...cp, candidateRouteIndex }
        : null;
    })
    .filter(Boolean)
    .sort((a, b) => a.routeIndex - b.routeIndex);

  return future[0] || null;
}

function isGlobalGoalModeActive(checkpoints, currentAIndex) {
  const intermediates = (checkpoints || []).filter(cp => !cp.isDestination);
  if (!intermediates.length) return true;

  const lastIntermediateIndex = Math.max(
    ...intermediates.map(cp => Number(cp.routeIndex))
  );

  // 「最終中間チェックポイント通過後」にGOALモードへ移行する。
  return Number(currentAIndex) >= lastIntermediateIndex;
}

export function evaluate({
  userA,
  candidate,
  checkpoints,
  currentAIndex,
  currentBIndex,
  elapsedSeconds,
  baseCum,
  candidateCum,
  baseRoute,
}) {
  const goalModeActive = isGlobalGoalModeActive(
    checkpoints,
    currentAIndex
  );
  const systemMode = goalModeActive ? 'GOAL_MODE' : 'NORMAL_MODE';

  const cp = firstFutureCommonCheckpoint({
    checkpoints,
    candidate,
    currentAIndex,
    currentBIndex,
    allowDestination: goalModeActive,
  });

  if (!cp) {
    return {
      eligible: false,
      reason: 'NO_FUTURE_COMMON_CHECKPOINT',
      systemMode,
      evaluationMode: 'NONE',
      weights: null,
      score: 0,
      simRoute: 0,
      simTime: 0,
      simSpatial: 0,
      cp: null,
      etaA: null,
      etaB: null,
      deltaEta: null,
      leadDeltaMinutes: null,
      candidateIsAhead: false,
      distanceKm: null,
    };
  }

  const remainingA = Math.max(
    0,
    userA.initialRemainingEtaSeconds - elapsedSeconds
  );
  const remainingB = Math.max(
    0,
    candidate.initialRemainingEtaSeconds - elapsedSeconds
  );

  const etaA = etaToIndexMinutes({
    cumulative: baseCum,
    currentIndex: currentAIndex,
    targetIndex: cp.routeIndex,
    remainingEtaSeconds: remainingA,
  });

  const etaB = etaToIndexMinutes({
    cumulative: candidateCum,
    currentIndex: currentBIndex,
    targetIndex: cp.candidateRouteIndex,
    remainingEtaSeconds: remainingB,
  });

  if (!Number.isFinite(etaA) || !Number.isFinite(etaB)) {
    return {
      eligible: false,
      reason: 'ETA_UNAVAILABLE',
      systemMode,
      evaluationMode: cp?.isDestination ? 'GOAL_MODE' : 'NORMAL_MODE',
      weights: cp?.isDestination ? CONFIG.goalWeights : CONFIG.normalWeights,
      score: 0,
      simRoute: 0,
      simTime: 0,
      simSpatial: 0,
      cp,
      etaA,
      etaB,
      deltaEta: null,
      leadDeltaMinutes: null,
      candidateIsAhead: false,
      distanceKm: null,
    };
  }

  const leadDeltaMinutes = etaA - etaB;
  const deltaEta = Math.abs(leadDeltaMinutes);
  const candidateIsAhead = leadDeltaMinutes > 0;

  const distanceKm = routeDistance(
    baseCum,
    currentAIndex,
    cp.routeIndex
  ) / 1000;

  const isGoalMode = goalModeActive && Boolean(cp.isDestination);
  const simRoute = isGoalMode
    ? 0
    : computeSimRouteByGrid({
        baseRoute,
        candidateRoute: candidate.route,
        currentAIndex,
        currentBIndex,
      });

  const simTime = computeSimTime(deltaEta);
  const simSpatial = computeSimSpatial(distanceKm);
  const weights = isGoalMode ? CONFIG.goalWeights : CONFIG.normalWeights;
  const score = computeScore(simRoute, simTime, simSpatial, weights);
  const gridsA = routeGridSet(baseRoute, currentAIndex);
  const gridsB = routeGridSet(candidate.route, currentBIndex);
  let commonGridCount = 0;
  gridsA.forEach(key => {
    if (gridsB.has(key)) commonGridCount += 1;
  });

  const eligible = candidateIsAhead && score >= CONFIG.threshold;
  let reason;
  if (!candidateIsAhead) reason = 'CANDIDATE_NOT_AHEAD';
  else if (score < CONFIG.threshold) reason = 'BELOW_THRESHOLD';
  else reason = 'MATCH';

  return {
    eligible,
    reason,
    candidateIsAhead,
    leadDeltaMinutes,
    systemMode,
    evaluationMode: isGoalMode ? 'GOAL_MODE' : 'NORMAL_MODE',
    weights,
    score,
    simRoute,
    simTime,
    simSpatial,
    cp,
    etaA,
    etaB,
    deltaEta,
    distanceKm,
    commonGridCount,
    gridCountA: gridsA.size,
    gridCountB: gridsB.size,
  };
}
