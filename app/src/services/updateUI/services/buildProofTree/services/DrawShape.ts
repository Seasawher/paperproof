import { Editor, TLShapeId, TLParentId, createShapeId } from "@tldraw/tldraw";

const arrow = (editor: Editor, fromId: TLShapeId, toId: TLShapeId, arrowType: "hypArrow" | "goalArrow" | "successArrow") => {
  editor.createShapes([
    {
      id: createShapeId(),
      type: "customArrow",
      props: {
        start: {
          type: 'binding', boundShapeId: fromId,
          normalizedAnchor: { x: 0.5, y: 1 },
          isExact: true
        },
        end: {
          type: 'binding', boundShapeId: toId,
          normalizedAnchor: { x: 0.5, y: 0 },
          isExact: true
        },
        size: "m"
      },
      meta: {
        arrowType
      }
    },
  ]);
}

const tactic = (editor: Editor,
  id: TLShapeId, parentId: TLParentId | undefined,
  x: number, y: number, w: number, h: number, text: string
) => {
  editor.createShapes([
    {
      id, type: "customNode", x, y, parentId,
      props: {
        geo: "rectangle", font: "mono", size: "m", w, h, text,

        dash: "dotted",
        fill: "solid",
        color: "grey",
      },
      meta: {
        type: "tactic"
      }
    },
  ]);
}

const goal = (editor: Editor,
  id: TLShapeId, parentId: TLParentId | undefined,
  x: number, y: number, w: number, h: number, text: string
) => {
  editor.createShapes([
    {
      id, type: "customNode", x, y, parentId,
      props: {
        geo: "rectangle", font: "mono", size: "m", w, h, text,

        dash: "solid",
        fill: "solid",
        color: "light-red"
      },
      meta: {
        type: "goal"
      }
    },
  ]);
}

const hypothesis = (editor: Editor,
  id: TLShapeId, parentId: TLParentId | undefined,
  x: number, y: number, w: number, h: number, text: string
) => {
  editor.createShapes([
    {
      id, type: "customNode", x, y, parentId,
      props: {
        geo: "rectangle", font: "mono", size: "m", w, h, text,

        dash: "solid",
        fill: "solid",
        color: "light-green"
      },
      meta: {
        type: "hypothesis"
      }
    },
  ]);
}

const window = (editor: Editor,
  id: TLShapeId, parentId: TLParentId | undefined,
  x: number, y: number, w: number, h: number, depth: number,
  goalUsername: string | null, goalUsernameHeight: number, windowId: string
) => {
  editor.createShapes([
    {
      id,
      type: "window",
      x,
      y,
      parentId,
      props: { w, h, depth, goalUsername, goalUsernameHeight, windowId },
    },
  ]);
}

export default { arrow, tactic, goal, hypothesis, window };
