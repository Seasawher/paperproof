import { TLParentId } from "@tldraw/tldraw";

import { HypTree, Element, IdElement, HypNode, HypLayer, Window, UiConfig, Shared } from "../../types";

import getHypNodeText from './getHypNodeText';
import hStack from './hStack';
import vStack from './vStack';
import byLevel from './byLevel';
import sum from './sum';
import getTreeWidth from './getTreeWidth';
import getTextSize from './getTextSize';

import { drawShapeWindow, drawShapeTactic, drawShapeGoal, drawShapeHypothesis } from './drawShape';

const inBetweenMargin = 20;
const framePadding = 20;

function shouldHide(node: HypNode, uiConfig: UiConfig) {
  return uiConfig.hideNulls ? node.id.includes("null") : false;
}

function withPadding(padding: { left: number, right: number, top: number, bottom: number }, el: Element): Element {
  return {
    size: [el.size[0] + padding.left + padding.right, el.size[1] + padding.top + padding.bottom],
    draw: (x, y) => {
      el.draw(x + padding.left, y + padding.top);
    }
  }
}

function withWidth(width: number, el: Element): Element {
  return { ...el, draw: (x, y) => { el.draw(x, y, width); } }
}

function emptyEl(): Element {
  return { size: [0, 0], draw: () => { } };
}

function trees(hMargin: number, ...trees: HypTree[]): Element {
  if (trees.length == 0) return { size: [0, 0], draw: () => { } };
  const rowHeights = byLevel(hMargin, trees).map(row => hStack(hMargin, ...row).size[1]);
  const colWidths = trees.map(t => getTreeWidth(hMargin, t));
  function draw(x: number, y: number, level: number, t: HypTree): void {
    if (level < t.level) {
      draw(x, y + rowHeights[level], level + 1, t);
      return;
    }
    const x0 = x;
    let lastNodeX = x;
    for (const node of t.nodes) {
      node.node.draw(x, y + t.tactic.size[1]);
      lastNodeX = x + node.node.size[0];
      const widths = [node.node.size[0]];
      if (node.tree) {
        draw(x, y + rowHeights[level], level + 1, node.tree);
        widths.push(getTreeWidth(hMargin, node.tree));
      }
      x += Math.max(...widths) + hMargin;
    }
    // We know the preffered width of the tactic only after we draw all the nodes (and their subtrees).
    // This is for cases like `match` or `induction` where the tactic should span all the underlying nodes.
    t.tactic.draw(x0, y, lastNodeX - x0);
  }
  return {
    size: [
      sum(colWidths, hMargin),
      sum(rowHeights)
    ],
    draw: (x, y) => {
      for (const tree of trees) {
        draw(x, y, 0, tree);
        x += getTreeWidth(hMargin, tree) + hMargin;
      }
    }
  };
}

const createNode = (
  shared: Shared,
  parentId: TLParentId | undefined,
  text: string,
  type: "hypothesis" | "tactic" | "goal",
  // This is for arrows
  externalId: string,
  ids: string[] = [],
): IdElement => {
  const id = shared.app.createShapeId(externalId);
  const [w, h] = getTextSize(shared.app, text);
  return {
    id,
    size: [w, h],
    draw(x, y, prefferedWidth?: number) {
      const isCurrentGoal = ids.includes(shared.currentGoal);
      const effectiveW = !!prefferedWidth && prefferedWidth > w ? prefferedWidth : w;
      if (type === "tactic") {
        drawShapeTactic(shared.app, id, parentId, x, y, effectiveW, h, text);
      } else if (type === "goal") {
        drawShapeGoal(shared.app, id, parentId, x, y, effectiveW, h, text, isCurrentGoal);
      } else if (type === "hypothesis") {
        drawShapeHypothesis(shared.app, id, parentId, x, y, effectiveW, h, text);
      }
    }
  }
};

export const createWindow = (shared: Shared, parentId: TLParentId | undefined, window: Window, depth: number): Element => {
  const frameId = shared.app.createShapeId(`window-${window.id}`);
  const nodes = withPadding(
    { left: framePadding, right: framePadding, top: framePadding, bottom: 0 },
    createNodes(shared, frameId, window, depth)
  );
  const title = createNode(shared, frameId, window.goalNodes[0].name, "tactic", `window-name-node-${window.id}`);
  const layout =
    localStorage.getItem("hideGoalUsernames") ?
      vStack(0, nodes) :
      vStack(0, nodes, withWidth(nodes.size[0], title));
  const [w, h] = layout.size;

  const draw = (x: number, y: number) => {
    drawShapeWindow(shared.app, frameId, parentId, x, y, w, h, depth);
    layout.draw(0, 0);
  };
  return { size: [w, h], draw };
}

function createNodes(shared: Shared, parentId: TLParentId | undefined, window: Window, depth: number): Element {
  let rows: Element[] = [];
  // Layers of hypNodes can have series of `rw` tactics where
  // we should attempt to stack nodes with the same name together.
  // We will assume that nodes in the same layer are generated by
  // the same tactic.
  function hasCommonNodes(as: HypLayer[], b: HypLayer) {
    const lastLayer = as[as.length - 1];
    const prevIds = shared.proofTree.tactics.flatMap(t => t.hypArrows.flatMap(a => b.some(toNode => a.toIds.includes(toNode.id)) && a.fromId ? a.fromId : []));
    return lastLayer.some(n => prevIds.includes(n.id));
  }
  const rwSeqs: HypLayer[][] = [];
  for (const layer of window.hypNodes) {
    if (rwSeqs.length > 0 && hasCommonNodes(rwSeqs[rwSeqs.length - 1], layer)) {
      rwSeqs[rwSeqs.length - 1].push(layer);
    } else {
      rwSeqs.push([layer]);
    }
  }
  // Have window can only be at the top level (since it never desctructs anything but each tactic after first in rwSeq does).
  for (const rwSeq of rwSeqs) {
    const topLevelTrees = new Set<HypTree>();
    const nodeToTree = new Map<string, HypTree>();
    for (let level = rwSeq.length - 1; level >= 0; level--) {
      const layer = rwSeq[level];
      const layerTactics = shared.proofTree.tactics
        .filter(tactic =>
          tactic.hypArrows.some(hypArrow =>
            layer.some(nodeAfter => hypArrow.toIds.includes(nodeAfter.id))
          )
        );
      if (layerTactics.length == 0) {
        // This is a weird case for the top level hypothesis which aren't generated by tactics. 
        topLevelTrees.add({
          tactic: emptyEl(), level, nodes: layer.map(
            node => {
              const hypNode = createNode(shared, parentId, getHypNodeText(node), "hypothesis", node.id);
              const tree = nodeToTree.get(node.id);
              if (tree) {
                topLevelTrees.delete(tree);
              }
              return { id: node.id, node: hypNode, tree };
            }
          )
        });
      }
      for (const tactic of layerTactics) {
        tactic.hypArrows.forEach((hypArrow) => {
          const nodesAfter = layer
            .filter((nodeAfter) => hypArrow.toIds.includes(nodeAfter.id))
            .filter(n => !shouldHide(n, shared.uiConfig));
          if (nodesAfter.length === 0) {
            return;
          }

          const tacticNode = createNode(
            shared,
            parentId,
            tactic.text,
            "tactic",
            `${tactic.id}${hypArrow.fromId}${parentId}`,
          );
          if (hypArrow.fromId) {
            shared.arrowsToDraw.push({ fromId: shared.app.createShapeId(hypArrow.fromId), toId: tacticNode.id });
          }
          nodesAfter.map(nodeAfter => {
            shared.arrowsToDraw.push({ fromId: tacticNode.id, toId: shared.app.createShapeId(nodeAfter.id) });
          });

          const haveWindows = shared.proofTree.windows
            .filter(w => tactic.haveWindowId === w.id)
            .map(w => createWindow(shared, parentId, w, depth + 1));
          const hTree: HypTree = {
            tactic: vStack(0, hStack(inBetweenMargin, ...haveWindows), tacticNode), level, nodes: nodesAfter.map(
              node => {
                const hypNode = createNode(shared, parentId, getHypNodeText(node), "hypothesis", node.id);
                const tree = nodeToTree.get(node.id);
                if (tree) {
                  topLevelTrees.delete(tree);
                }
                return { id: node.id, node: hypNode, tree };
              }
            )
          }
          if (hypArrow.fromId) {
            nodeToTree.set(hypArrow.fromId, hTree)
          }
          topLevelTrees.add(hTree);
        });
      }
    }
    if (topLevelTrees.size > 0) {
      // Reverse because we were adding them bottom up but should prefer those which start earlier.
      rows.push(trees(inBetweenMargin, ...[...topLevelTrees.values()].reverse()));
    }
  }
  const subWindows = shared.proofTree.windows.filter((w) => w.parentId == window.id);
  const frames: Element[] = [];
  for (const subWindow of subWindows) {
    frames.push(createWindow(shared, parentId, subWindow, depth + 1));
  }
  const goalNodes = [...window.goalNodes].reverse();
  const proof: Element[] = goalNodes.flatMap(goalNode => {
    const tactic = shared.proofTree.tactics.find(
      (t) =>
        t.goalArrows.some((a) => a.fromId == goalNode.id) ||
        t.successGoalId == goalNode.id
    );
    const id = localStorage.getItem("dev") === 'true'
      ? ' ' + goalNode.id
      : '';
    const goalEl: Element = createNode(
      shared,
      parentId,
      goalNode.text + id,
      "goal",
      goalNode.id,
      [goalNode.id]
    );
    return [tactic ?
      createNode(
        shared,
        parentId,
        tactic.text + (tactic.successGoalId ? " 🎉" : ""),
        "tactic",
        tactic.id,
      )
      : [], goalEl].flat();
  });
  if (frames.length > 0) {
    // In such case we want to attach last tactic to the row with frames
    const framesEl = hStack(inBetweenMargin, ...frames);
    // We can assume that the first element is a tactic since we have frames.
    rows.push(vStack(0, framesEl, withWidth(framesEl.size[0], proof[0]), ...proof.slice(1)));
  } else {
    const goals = vStack(0, ...proof);
    rows.push(goals);
  }
  return vStack(inBetweenMargin, ...rows);
}
