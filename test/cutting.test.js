'use strict';

// 批量裁切下料纯函数测试：印张数校验、矩形分割搜索（对拍网格暴力解）、
// 贯通裁切树几何有效性、原纸方向枚举、尾张余量与废料、推荐排序与不可行原因。
const assert = require('assert');
const {
  PT_PER_MM,
  MAX_REQUIRED_SHEETS,
  MAX_ITEMS_PER_SHEET,
  FIT_EPSILON_MM,
  parseRequiredSheets,
  solveGuillotine,
  refineCutTree,
  positionTree,
  buildCuttingPlan,
} = require('../lib/cutting');

const PANEL_A4 = { width: 595.2756, height: 841.8898, orientation: 'portrait' };
const planA4 = {
  sheets: [{ sheet: 1 }, { sheet: 2 }],
  sourceCount: 8, paddedCount: 0, totalCount: 8, blanks: 0,
  panel: PANEL_A4,
  sheet: { width: 595.2756 * 2, height: 841.8898 },
};
const P = (name, widthMm, heightMm) => ({
  name, widthMm, heightMm, pricePerSheet: 0, setupFee: 0,
});

// ---------- 1. 所需印张数校验 ----------

assert.strictEqual(parseRequiredSheets(1), 1);
assert.strictEqual(parseRequiredSheets(' 42 '), 42);
assert.strictEqual(parseRequiredSheets(MAX_REQUIRED_SHEETS), MAX_REQUIRED_SHEETS);
for (const bad of [0, -1, 1.5, 'abc', '', ' ', null, undefined, true, '1e3', 1.0001, MAX_REQUIRED_SHEETS + 1]) {
  assert.throws(() => parseRequiredSheets(bad), /所需印张数必须是/, `应拒绝 ${JSON.stringify(bad)}`);
}

// ---------- 2. 分割搜索：与整数网格暴力 guillotine 解对拍 ----------

function bruteGuillotine(W, H, a, b, memo) {
  const key = `${W}x${H}`;
  if (memo.has(key)) return memo.get(key);
  const fit1 = W >= a && H >= b;
  const fit2 = W >= b && H >= a;
  if (!fit1 && !fit2) { memo.set(key, 0); return 0; }
  let best = 1;
  for (const d of [a, b]) {
    for (let k = 1; k * d < W; k += 1) {
      if (k * d <= W / 2) {
        best = Math.max(best,
          bruteGuillotine(k * d, H, a, b, memo) + bruteGuillotine(W - k * d, H, a, b, memo));
      }
    }
    for (let k = 1; k * d < H; k += 1) {
      if (k * d <= H / 2) {
        best = Math.max(best,
          bruteGuillotine(W, k * d, a, b, memo) + bruteGuillotine(W, H - k * d, a, b, memo));
      }
    }
  }
  memo.set(key, best);
  return best;
}

for (let W = 1; W <= 18; W += 1) {
  for (let H = 1; H <= 18; H += 1) {
    for (let a = 2; a <= 7; a += 1) {
      for (let b = 2; b <= 7; b += 1) {
        const got = solveGuillotine(W, H, a, b, new Map(), { states: 0 });
        const ref = bruteGuillotine(W, H, a, b, new Map());
        assert.strictEqual(
          got.count, ref,
          `W=${W},H=${H},a=${a},b=${b} 搜索产出 ${got.count} ≠ 暴力解 ${ref}`,
        );
      }
    }
  }
}

// ---------- 3. 裁切树：叶节点铺满根矩形，坐标无重叠、不越界、切线贯通 ----------

function flattenLeaves(node, x = 0, y = 0, out = []) {
  if (node.kind === 'leaf') {
    out.push({
      x, y, w: node.width, h: node.height, used: node.used,
      rotated: node.rotated, itemW: node.itemW, itemH: node.itemH,
    });
    return out;
  }
  if (node.direction === 'v') {
    flattenLeaves(node.first, x, y, out);
    flattenLeaves(node.second, x + node.offset, y, out);
  } else {
    flattenLeaves(node.first, x, y, out);
    flattenLeaves(node.second, x, y + node.offset, out);
  }
  return out;
}

/**
 * 递归收集「裁切线 + 其所在矩形边界」：后续刀只贯通当前子条而非整张原纸。
 */
function flattenCuts(node, x = 0, y = 0, out = []) {
  if (node.kind === 'leaf') return out;
  if (node.direction === 'v') {
    out.push({
      direction: 'v',
      x1: x + node.offset, y1: y, x2: x + node.offset, y2: y + node.height,
      pieceX: x, pieceY: y, pieceW: node.width, pieceH: node.height,
    });
    flattenCuts(node.first, x, y, out);
    flattenCuts(node.second, x + node.offset, y, out);
  } else {
    out.push({
      direction: 'h',
      x1: x, y1: y + node.offset, x2: x + node.width, y2: y + node.offset,
      pieceX: x, pieceY: y, pieceW: node.width, pieceH: node.height,
    });
    flattenCuts(node.first, x, y, out);
    flattenCuts(node.second, x, y + node.offset, out);
  }
  return out;
}

/**
 * 模拟现场按 cuts 先序逐刀裁切：每刀必须贯通手上一块真实存在的料件
 * （沿其整个高度竖切或整个宽度横切），切后两块新料件替代原料件；
 * 全部切完后，每块终端料件要么恰好是一片印张、要么是一块废料。
 * 这直接保证「印张能与边料分离」且刀线按料件顺序可执行。
 */
function simulateCuts(W, H, items, wastes, cuts) {
  let pieces = [{ x: 0, y: 0, w: W, h: H }];
  for (const cut of cuts) {
    const idx = pieces.findIndex((p) => (
      Math.abs(p.x - cut.pieceXMm) < 1e-6
      && Math.abs(p.y - cut.pieceYMm) < 1e-6
      && Math.abs(p.w - cut.pieceWidthMm) < 1e-6
      && Math.abs(p.h - cut.pieceHeightMm) < 1e-6
    ));
    assert.ok(idx >= 0, `第 ${cuts.indexOf(cut) + 1} 刀所在料件不在手持料件中（顺序不可执行）`);
    const p = pieces[idx];
    if (cut.direction === 'v') {
      assert.ok(Math.abs(cut.x1Mm - cut.x2Mm) < 1e-9, '竖切线不直');
      assert.ok(Math.abs(cut.y1Mm - p.y) < 1e-6 && Math.abs(cut.y2Mm - (p.y + p.h)) < 1e-6,
        '竖切线未贯通料件高度');
      assert.ok(cut.x1Mm > p.x + 1e-6 && cut.x1Mm < p.x + p.w - 1e-6, '竖切线不在料件内部');
      const offset = cut.x1Mm - p.x;
      pieces.splice(idx, 1,
        { x: p.x, y: p.y, w: offset, h: p.h },
        { x: p.x + offset, y: p.y, w: p.w - offset, h: p.h });
    } else {
      assert.ok(Math.abs(cut.y1Mm - cut.y2Mm) < 1e-9, '横切线不直');
      assert.ok(Math.abs(cut.x1Mm - p.x) < 1e-6 && Math.abs(cut.x2Mm - (p.x + p.w)) < 1e-6,
        '横切线未贯通料件宽度');
      assert.ok(cut.y1Mm > p.y + 1e-6 && cut.y1Mm < p.y + p.h - 1e-6, '横切线不在料件内部');
      const offset = cut.y1Mm - p.y;
      pieces.splice(idx, 1,
        { x: p.x, y: p.y, w: p.w, h: offset },
        { x: p.x, y: p.y + offset, w: p.w, h: p.h - offset });
    }
  }
  const terminals = [...items.map((r) => ({ ...r, kind: 'item' })),
    ...wastes.map((r) => ({ ...r, kind: 'waste' }))];
  assert.strictEqual(pieces.length, terminals.length,
    `终端料件 ${pieces.length} ≠ 印张+废料 ${terminals.length}`);
  for (const p of pieces) {
    const hit = terminals.find((r) => (
      Math.abs(p.x - r.xMm) < 1e-6 && Math.abs(p.y - r.yMm) < 1e-6
      && Math.abs(p.w - r.widthMm) < 1e-6 && Math.abs(p.h - r.heightMm) < 1e-6
    ));
    assert.ok(hit, `终端料件 ${p.x},${p.y} ${p.w}×${p.h} 既不是印张也不是废料`);
  }
}

function validateTree(W, H, a, b) {
  const result = solveGuillotine(W, H, a, b, new Map(), { states: 0 });
  const refined = refineCutTree(result.tree);
  const leaves = flattenLeaves(refined);

  // 叶节点无缝铺满根矩形（面积守恒）
  const area = leaves.reduce((sum, l) => sum + l.w * l.h, 0);
  assert.ok(Math.abs(area - W * H) < 1e-6, `叶面积 ${area} ≠ 根面积 ${W * H}`);

  // 展开后：占用叶严格等于一片印张（所在料件不再大于印张），
  // 废料叶 used=false；每个占用叶尺寸为 a×b 或 b×a
  for (const l of leaves) {
    if (l.used) {
      assert.ok(Math.abs(l.w - l.itemW) < 1e-9 && Math.abs(l.h - l.itemH) < 1e-9,
        '占用叶未与余料分离（所在料件仍大于印张）');
      const dims = l.rotated ? [b, a] : [a, b];
      assert.ok(Math.abs(l.w - dims[0]) < 1e-6 && Math.abs(l.h - dims[1]) < 1e-6,
        '占用叶尺寸与印张不一致');
    }
  }

  const out = { items: [], wastes: [], cuts: [] };
  positionTree(refined, 0, 0, out);
  assert.strictEqual(out.items.length, result.count);

  // 每个印张尺寸为 a×b 或 b×a，且不越界
  for (const it of out.items) {
    const dw = it.rotated ? Math.abs(it.widthMm - b) : Math.abs(it.widthMm - a);
    const dh = it.rotated ? Math.abs(it.heightMm - a) : Math.abs(it.heightMm - b);
    assert.ok(dw < 1e-6 && dh < 1e-6, '印张尺寸与方向不一致');
    assert.ok(it.xMm >= -1e-6 && it.yMm >= -1e-6
      && it.xMm + it.widthMm <= W + 1e-6 && it.yMm + it.heightMm <= H + 1e-6, '印张越界');
  }
  // 两两不重叠（严格分离，非面积估算/重叠摆放）
  for (let i = 0; i < out.items.length; i += 1) {
    for (let j = i + 1; j < out.items.length; j += 1) {
      const p = out.items[i];
      const q = out.items[j];
      const overlap = p.xMm < q.xMm + q.widthMm - 1e-6
        && q.xMm < p.xMm + p.widthMm - 1e-6
        && p.yMm < q.yMm + q.heightMm - 1e-6
        && q.yMm < p.yMm + p.heightMm - 1e-6;
      assert.ok(!overlap, `印张 ${i} 与 ${j} 重叠`);
    }
  }
  // 每条裁切线都贯通其所在矩形（首刀贯通整张原纸，其后贯通当前子条），
  // 并按先序模拟现场逐刀裁切：刀线顺序可执行，切完只剩印张与废料
  const allCuts = flattenCuts(refined);
  assert.strictEqual(allCuts.length, out.cuts.length, '裁切线数量一致');
  for (const cut of allCuts) {
    if (cut.direction === 'v') {
      assert.ok(Math.abs(cut.x1 - cut.x2) < 1e-9, '竖切线不直');
      assert.ok(cut.x1 > cut.pieceX && cut.x1 < cut.pieceX + cut.pieceW, '竖切线不在料件内部');
      assert.ok(Math.abs(cut.y1 - cut.pieceY) < 1e-9
        && Math.abs(cut.y2 - (cut.pieceY + cut.pieceH)) < 1e-9, '竖切线未贯通料件');
    } else {
      assert.ok(Math.abs(cut.y1 - cut.y2) < 1e-9, '横切线不直');
      assert.ok(cut.y1 > cut.pieceY && cut.y1 < cut.pieceY + cut.pieceH, '横切线不在料件内部');
      assert.ok(Math.abs(cut.x1 - cut.pieceX) < 1e-9
        && Math.abs(cut.x2 - (cut.pieceX + cut.pieceW)) < 1e-9, '横切线未贯通料件');
    }
  }
  simulateCuts(W, H, out.items, out.wastes, out.cuts);
  return { result, refined };
}

for (const [W, H, a, b] of [
  [100, 100, 40, 30], [250, 180, 100, 60], [300, 300, 200, 100],
  [500, 300, 300, 200], [889, 1194, 420, 297], [1000, 707, 420, 297],
  [350, 250, 300, 200],
]) {
  validateTree(W, H, a, b);
}

// 放不下：0 产出，整矩形为废料叶
const none = solveGuillotine(100, 50, 200, 30, new Map(), { states: 0 });
assert.strictEqual(none.count, 0);
assert.strictEqual(none.tree.kind, 'leaf');
assert.strictEqual(none.tree.used, false);

// 恰好放下：叶节点直接为 1 个印张，零裁切、零废料
const exact = solveGuillotine(420, 297, 420, 297, new Map(), { states: 0 });
assert.strictEqual(exact.count, 1);
assert.strictEqual(exact.tree.kind, 'leaf');
const exactOut = { items: [], wastes: [], cuts: [] };
positionTree(refineCutTree(exact.tree), 0, 0, exactOut);
assert.strictEqual(exactOut.cuts.length, 0);
assert.strictEqual(exactOut.wastes.length, 0);

// 漏刀回归：350×250 原纸裁 300×200 印张——印张两维都小于原纸，必须补
// 一竖一横两刀把右侧 50mm 边条与上方 50mm 边条分离为废料（修复前 cutCount=0）
const loose = solveGuillotine(350, 250, 300, 200, new Map(), { states: 0 });
assert.strictEqual(loose.count, 1);
const looseRefined = refineCutTree(loose.tree);
assert.strictEqual(looseRefined.kind, 'cut');
assert.strictEqual(looseRefined.direction, 'v');
assert.strictEqual(looseRefined.offset, 300);
const looseOut = { items: [], wastes: [], cuts: [] };
positionTree(looseRefined, 0, 0, looseOut);
assert.strictEqual(looseOut.items.length, 1);
assert.strictEqual(looseOut.cuts.length, 2);
assert.strictEqual(looseOut.wastes.length, 2);
simulateCuts(350, 250, looseOut.items, looseOut.wastes, looseOut.cuts);
const looseWasteArea = looseOut.wastes.reduce((s, w) => s + w.widthMm * w.heightMm, 0);
assert.strictEqual(looseWasteArea, 350 * 250 - 300 * 200);
// 第一刀贯通整张原纸竖切，第二刀在切出的 300×250 左条内横切
assert.deepStrictEqual(
  looseOut.cuts.map((c) => [c.direction, c.x1Mm, c.y1Mm, c.pieceWidthMm, c.pieceHeightMm]),
  [['v', 300, 0, 350, 250], ['h', 0, 200, 300, 250]],
);

// 只在一个方向富余：只补一刀（宽富余竖切；高富余横切）
function cutSummary(W, H, a, b) {
  const r = refineCutTree(solveGuillotine(W, H, a, b, new Map(), { states: 0 }).tree);
  const o = { items: [], wastes: [], cuts: [] };
  positionTree(r, 0, 0, o);
  return o;
}
const onlyW = cutSummary(320, 200, 300, 200);
assert.strictEqual(onlyW.cuts.length, 1);
assert.strictEqual(onlyW.cuts[0].direction, 'v');
assert.strictEqual(onlyW.wastes.length, 1);
assert.deepStrictEqual(
  { x: onlyW.wastes[0].xMm, y: onlyW.wastes[0].yMm,
    w: onlyW.wastes[0].widthMm, h: onlyW.wastes[0].heightMm },
  { x: 300, y: 0, w: 20, h: 200 },
);
const onlyH = cutSummary(300, 230, 300, 200);
assert.strictEqual(onlyH.cuts.length, 1);
assert.strictEqual(onlyH.cuts[0].direction, 'h');
assert.strictEqual(onlyH.wastes.length, 1);
assert.deepStrictEqual(
  { x: onlyH.wastes[0].xMm, y: onlyH.wastes[0].yMm,
    w: onlyH.wastes[0].widthMm, h: onlyH.wastes[0].heightMm },
  { x: 0, y: 200, w: 300, h: 30 },
);

// 经典排布：600×800 内放 300×200 恰好 8 个
assert.strictEqual(solveGuillotine(600, 800, 300, 200, new Map(), { states: 0 }).count, 8);

// ---------- 4. buildCuttingPlan：整体方案、尾张与废料 ----------

const cut = buildCuttingPlan(planA4, [
  P('A3', 420, 297),         // 恰好 1 个
  P('大度对开', 889, 1194),  // 8 个（420 两列 × 297 四行）
  P('A4 太小', 297, 210),    // 不可行
], 100);
assert.strictEqual(cut.kind, 'sheet-cutting-plan');
assert.strictEqual(cut.schemaVersion, 1);
assert.strictEqual(cut.feasible, true);
assert.strictEqual(cut.requiredSheets, 100);

const a3 = cut.options[0];
assert.strictEqual(a3.feasible, true);
assert.strictEqual(a3.yieldsPerSheet, 1);
assert.strictEqual(a3.sheetsRequired, 100);
assert.strictEqual(a3.lastSheet.isLastSheetPartial, false);
assert.strictEqual(a3.lastSheet.exact, true);
assert.strictEqual(a3.lastSheet.spareCapacity, 0);
assert.strictEqual(a3.waste.perSheetAreaMm2, 0); // 恰好铺满，废料严格为 0
assert.strictEqual(a3.waste.totalAreaMm2, 0);
assert.strictEqual(a3.utilizationPercent, 100);
assert.strictEqual(a3.cutting.cutCount, 0);
assert.strictEqual(a3.cutting.items.length, 1);

const big = cut.options[1];
assert.strictEqual(big.yieldsPerSheet, 8);
assert.strictEqual(big.sheetsRequired, 13); // ceil(100/8)
assert.strictEqual(big.lastSheet.fullSheets, 12);
assert.strictEqual(big.lastSheet.lastSheetYield, 4);
assert.strictEqual(big.lastSheet.spareCapacity, 4);
assert.strictEqual(big.lastSheet.isLastSheetPartial, true);
// 8 个 420×297 = 840×1188 条带铺满可行条带；889×1194 原纸周边有余料
const round2 = (v) => Math.round((v + Number.EPSILON) * 100) / 100;
const perSheetWaste = 889 * 1194 - 8 * 420 * 297;
assert.ok(Math.abs(big.waste.perSheetAreaMm2 - round2(perSheetWaste)) < 1,
  `单张废料 ${big.waste.perSheetAreaMm2} ≈ ${round2(perSheetWaste)}`);
assert.ok(big.waste.lastSheetAreaMm2 > big.waste.perSheetAreaMm2, '尾张废料含 4 个空位');
// 总废料 = 12 张满排废料 + 1 张尾张废料（尾张只裁 4 个）
const expectedTotal = 12 * big.waste.perSheetAreaMm2 + big.waste.lastSheetAreaMm2;
assert.ok(Math.abs(big.waste.totalAreaMm2 - round2(expectedTotal)) < 1,
  `总废料 ${big.waste.totalAreaMm2} ≈ ${round2(expectedTotal)}`);
assert.strictEqual(big.cutting.items.length, 8);

// 漏刀回归（现场场景）：350×250 mm 原纸裁 300×200 mm 印张——可行且出 1 个，
// 但修复前 cutCount=0、占用叶覆盖整张原纸，印张无法与边料分离。
// 修复后必须给出 2 刀贯通裁切（先竖切分离 50mm 右边料，再在左条横切分离
// 50mm 上边料），两块边料标为废料，items/cuts/tree 坐标尺寸一致。
const planLoose = {
  sheets: [{ sheet: 1 }],
  sourceCount: 4, paddedCount: 0, totalCount: 4, blanks: 0,
  panel: { width: 150 * PT_PER_MM, height: 200 * PT_PER_MM, orientation: 'portrait' },
  sheet: { width: 300 * PT_PER_MM, height: 200 * PT_PER_MM },
};
const loosePlan = buildCuttingPlan(planLoose, [P('边料原纸', 350, 250)], 1);
assert.strictEqual(loosePlan.feasible, true);
const lo = loosePlan.options[0];
assert.strictEqual(lo.yieldsPerSheet, 1);
assert.strictEqual(lo.cutting.cutCount, 2);
assert.strictEqual(lo.cutting.items.length, 1);
assert.strictEqual(lo.cutting.wastes.length, 2);
// 废料面积守恒：两块边料合计 = 原纸 − 印张 = 27,500 mm²
const looseWaste = lo.cutting.wastes.reduce((s, w) => s + w.widthMm * w.heightMm, 0);
assert.ok(Math.abs(looseWaste - (350 * 250 - 300 * 200)) < 0.01,
  `边料合计 ${looseWaste} ≠ 27500`);
assert.ok(Math.abs(lo.waste.perSheetAreaMm2 - 27500) < 0.01);
// 印张 + 废料无缝铺满原纸（坐标尺寸一致，无重叠无空隙）
const tiled = lo.cutting.items.reduce((s, r) => s + r.widthMm * r.heightMm, 0)
  + lo.cutting.wastes.reduce((s, r) => s + r.widthMm * r.heightMm, 0);
assert.ok(Math.abs(tiled - 350 * 250) < 0.01);
// 刀线按当前料件顺序可执行：第 1 刀贯通整张原纸，第 2 刀贯通切出的 300×250 料件
assert.deepStrictEqual(
  lo.cutting.cuts.map((c) => [
    c.direction, c.pieceWidthMm, c.pieceHeightMm,
    Math.round((c.x1Mm - c.pieceXMm) * 100) / 100,
    Math.round((c.y1Mm - c.pieceYMm) * 100) / 100,
  ]),
  [['v', 350, 250, 300, 0], ['h', 300, 250, 0, 200]],
);
// tree 与 items/cuts 同源一致：叶节点数 = 1 印张 + 2 废料
const countTreeLeaves = (n) => (n.kind === 'leaf' ? 1
  : countTreeLeaves(n.first) + countTreeLeaves(n.second));
assert.strictEqual(countTreeLeaves(lo.cutting.tree), 3);
assert.strictEqual(lo.cutting.tree.first.first.used, true);
assert.strictEqual(lo.cutting.tree.first.second.used, false);
assert.strictEqual(lo.cutting.tree.second.used, false);

// 整除时无尾张：总废料 = 每张常规废料 × 张数
const exactRun = buildCuttingPlan(planA4, [P('大度对开', 889, 1194)], 16);
const big16 = exactRun.options[0];
assert.strictEqual(big16.sheetsRequired, 2);
assert.strictEqual(big16.lastSheet.isLastSheetPartial, false);
assert.strictEqual(big16.lastSheet.lastSheetYield, 0);
assert.ok(Math.abs(big16.waste.totalAreaMm2 - 2 * big16.waste.perSheetAreaMm2) < 0.01);

// ---------- 5. 推荐排序：所需原纸张数 → 总废料面积 ----------

const ranked = buildCuttingPlan(planA4, [
  P('大但废料多', 600, 1000),  // 4 个 → 25 张
  P('大度对开', 889, 1194),   // 8 个 → 13 张
  P('A3', 420, 297),         // 1 个 → 100 张
], 100);
const feasible = ranked.options.filter((o) => o.feasible);
// options 保持维护顺序；推荐项由 recommended 指定（按张数、废料排序）
assert.strictEqual(ranked.recommended.name, '大度对开');
const rec = ranked.options.find((o) => o.index === ranked.recommended.index);
assert.strictEqual(rec.yieldsPerSheet, 8);
assert.strictEqual(rec.sheetsRequired, 13);
assert.ok(rec.sheetsRequired < feasible.find((o) => o.name === '大但废料多').sheetsRequired);

// 所需张数相同（单张产出相同）时按总废料面积升序：
// 841×1190 与 880×1188 都出 8 个，但前者废料更少
const tie = buildCuttingPlan(planA4, [
  P('大纸 A 废料多', 880, 1188),
  P('大纸 B 废料少', 841, 1188),
], 8);
const t0 = tie.options.find((o) => o.name === '大纸 A 废料多');
const t1 = tie.options.find((o) => o.name === '大纸 B 废料少');
assert.strictEqual(t0.yieldsPerSheet, t1.yieldsPerSheet);
assert.strictEqual(t0.sheetsRequired, t1.sheetsRequired);
assert.ok(t1.waste.totalAreaMm2 < t0.waste.totalAreaMm2,
  `废料排序 ${t1.waste.totalAreaMm2} 应 < ${t0.waste.totalAreaMm2}`);
assert.strictEqual(tie.recommended.name, '大纸 B 废料少');

// ---------- 6. 旋转：竖放原纸与混合朝向排布 ----------

// 297×420 的「竖 A3」原纸：纸张保持原向、印张旋转 90°（297×420）即可放下；
// 纸张旋转 90°（420×297）时印张原向放入——两方向产出相同，优先纸张原向
const portrait = buildCuttingPlan(planA4, [P('竖 A3', 297, 420)], 3);
assert.strictEqual(portrait.feasible, true);
assert.strictEqual(portrait.options[0].yieldsPerSheet, 1);
assert.strictEqual(portrait.options[0].placement.orientation, 'as_is');
assert.strictEqual(portrait.options[0].placement.rotated, false);
assert.strictEqual(portrait.options[0].placement.rotatedItemCount, 1);

// 纸张旋转 90° 与原向产出相同：420×594 横 A2 与 594×420 竖 A2 都出 2 个，
// 横纸选原向；这保证两个方向都被枚举（结果与整体旋转对称）
const bothDirs = buildCuttingPlan(planA4, [
  P('横 A2', 594, 420),
  P('竖 A2', 420, 594),
], 3);
for (const o of bothDirs.options) {
  assert.strictEqual(o.feasible, true);
  assert.strictEqual(o.yieldsPerSheet, 2);
  assert.strictEqual(o.placement.orientation, 'as_is');
}

// 窄纸 300×400：纸张原向与旋转 90° 后两个朝向都放不下（两个朝向都缺
// 420 那条边）——不可行并给出两方向不足量，原因不混淆
const narrow = buildCuttingPlan(planA4, [P('窄纸 300×400', 300, 400)], 3);
assert.strictEqual(narrow.feasible, false);
assert.strictEqual(narrow.reasonCode, 'no_fitting_paper');
assert.match(narrow.reason, /300 × 400/);

// 同一朝向内混合旋转：500×300 内放 300×200，左侧原向 1 个 +
// 右侧 200×300 条带内印张旋转 90° 再出 1 个 → 共 2 个（面积上界也是 2）
const plan300x200 = {
  sheets: [{ sheet: 1 }],
  sourceCount: 4, paddedCount: 0, totalCount: 4, blanks: 0,
  panel: { width: 150 * PT_PER_MM, height: 200 * PT_PER_MM, orientation: 'portrait' },
  sheet: { width: 300 * PT_PER_MM, height: 200 * PT_PER_MM },
};
const mixed = buildCuttingPlan(plan300x200, [P('混合朝向原纸', 500, 300)], 1);
const m = mixed.options[0];
assert.strictEqual(m.yieldsPerSheet, 2);
assert.ok(m.placement.rotatedItemCount >= 1, '混合朝向方案应包含旋转印张');

// ---------- 7. 不可行：明确原因（两个方向的不足量） ----------

const noFit = buildCuttingPlan(planA4, [P('A4', 297, 210)], 10);
assert.strictEqual(noFit.feasible, false);
assert.strictEqual(noFit.recommended, null);
assert.strictEqual(noFit.reasonCode, 'no_fitting_paper');
assert.match(noFit.reason, /420/);
assert.match(noFit.reason, /A4/);
const opt = noFit.options[0];
assert.strictEqual(opt.feasible, false);
assert.strictEqual(opt.reasons.length, 2);
const asIs = opt.reasons.find((r) => r.orientation === 'as_is');
const rotated = opt.reasons.find((r) => r.orientation === 'rotated_90');
assert.ok(asIs.shortageWidthMm > 0 && asIs.shortageHeightMm > 0);
assert.match(asIs.message, /宽度不足/);
assert.match(rotated.message, /宽度不足/);

// ---------- 8. 非法入参 ----------

assert.throws(() => buildCuttingPlan(null, [P('A3', 420, 297)], 1), /plan/);
assert.throws(() => buildCuttingPlan(planA4, [], 1), /至少维护一种/);
assert.throws(() => buildCuttingPlan(planA4, [P('坏', 0, 100)], 1), /宽必须是大于 0/);
assert.throws(() => buildCuttingPlan(planA4, [P('A3', 420, 297)], 0), /所需印张数/);
assert.throws(() => buildCuttingPlan(planA4, [P('A3', 420, 297)], 1.2), /所需印张数/);
assert.throws(
  () => buildCuttingPlan(planA4, Array(9).fill(P('x', 420, 297)), 1),
  /最多维护 8 种/,
);

// ---------- 9. 规模上限 ----------

const huge = buildCuttingPlan({
  sheets: [{ sheet: 1 }],
  sourceCount: 4, paddedCount: 0, totalCount: 4, blanks: 0,
  panel: { width: 100, height: 100, orientation: 'square' },
  sheet: { width: 200, height: 100 }, // 极小印张（pt）
}, [P('巨型原纸', 100000, 100000)], 1);
// 面积上界超过 MAX_ITEMS_PER_SHEET：该规格不给出方案
assert.strictEqual(huge.feasible, false);
assert.strictEqual(MAX_ITEMS_PER_SHEET > 0, true);
assert.ok(FIT_EPSILON_MM > 0);

// ---------- 10. 结构稳定性（JSON 可序列化、外部消费字段齐全） ----------

const json = JSON.parse(JSON.stringify(cut));
assert.strictEqual(json.kind, 'sheet-cutting-plan');
assert.strictEqual(typeof json.generatedAt, 'string');
assert.ok(json.layout.sheet.widthMm > 0 && json.layout.sheet.heightMm > 0);
for (const o of json.options) {
  if (o.feasible) {
    assert.ok(Number.isInteger(o.yieldsPerSheet) && o.yieldsPerSheet > 0);
    assert.ok(Number.isInteger(o.sheetsRequired) && o.sheetsRequired > 0);
    assert.ok(Array.isArray(o.cutting.items) && o.cutting.items.length === o.yieldsPerSheet);
    assert.ok(Array.isArray(o.cutting.wastes));
    assert.ok(Array.isArray(o.cutting.cuts));
    assert.ok(Number.isInteger(o.cutting.cutCount));
    assert.strictEqual(o.cutting.cutCount, o.cutting.cuts.length);
    assert.ok(o.cutting.tree && typeof o.cutting.tree.kind === 'string');
    assert.ok(o.waste.totalAreaMm2 >= 0);
    // items + wastes 铺满原纸且互不重叠；废料面积与 wastes 几何合计一致
    const frameArea = o.cutting.frame.widthMm * o.cutting.frame.heightMm;
    const itemArea = o.cutting.items.reduce((s, r) => s + r.widthMm * r.heightMm, 0);
    const wasteArea = o.cutting.wastes.reduce((s, r) => s + r.widthMm * r.heightMm, 0);
    assert.ok(Math.abs(itemArea + wasteArea - frameArea) < 0.5,
      'items + wastes 未铺满原纸');
    assert.ok(Math.abs(wasteArea - o.waste.perSheetAreaMm2) < 0.5,
      'wastes 几何合计与废料面积不一致');
    const rects = [
      ...o.cutting.items.map((r) => ({ ...r, waste: false })),
      ...o.cutting.wastes.map((r) => ({ ...r, waste: true })),
    ];
    for (let i = 0; i < rects.length; i += 1) {
      for (let j = i + 1; j < rects.length; j += 1) {
        const p = rects[i];
        const q = rects[j];
        const overlap = p.xMm < q.xMm + q.widthMm - 1e-6
          && q.xMm < p.xMm + p.widthMm - 1e-6
          && p.yMm < q.yMm + q.heightMm - 1e-6
          && q.yMm < p.yMm + p.heightMm - 1e-6;
        assert.ok(!overlap, '印张与废料（或两块区域）重叠');
      }
    }
  } else {
    assert.strictEqual(o.yieldsPerSheet, undefined);
  }
}

// pt↔mm 换算自检
assert.ok(Math.abs(PT_PER_MM - 72 / 25.4) < 1e-12);

console.log('✅ 批量裁切下料纯函数测试通过：印张数校验、记忆化矩形分割搜索（网格暴力对拍）、');
console.log('   贯通裁切树（铺满/无重叠/不越界/切线贯通）、原纸方向枚举与混合旋转、');
console.log('   单张产出/所需原纸/尾张余量/废料面积、推荐排序、不可行原因与规模上限');
