// Thanks David <3
/*
abstract sig A, B {}
one sig A1, A2, A3 extends A {}
one sig B1, B2 extends B {}
one sig R {
  r: A some -> lone B
} {
  //r[A1] = r[A2] && r[A1] = B1
  // same as
  //A1.r = A2.r && A1.r = B1
  //r.B1 = r.B2
}

run {} for 4

sig Node {}
sig DAG {
  edge: Node -> Node
}

pred add(g0, g1: DAG, e: Node -> Node) {
  one e
  g1.edge = g0.edge + e
}

fact acyclic {
  all g: DAG | no n: Node | n in n.^(g.edge)
}

run add for 3 but 2 DAG
/*
a) ANALYSIS VARIABLES:

  signatures: Node, DAG
  field: edge
  arguments: g0, g1 and e

b) ANALYSIS CONSTRAINT:
  no Node & and

  g in DAG and
  g' in DAG and
  e in Node -> Node and

  one e and
  g'.edge = g.edge p + and
  all g: DAG | no n:Node | n in n.^(g.edge)
*/

sig Tree {
  root: lone TreeNode
}
sig TreeNode {
  left, right: lone TreeNode,
  value: one Int
}

fun parent: TreeNode -> TreeNode {
  {n, p: TreeNode | n->p in (n -> left.n + n -> right.n)}
}

// for extra readibilty
fun children: TreeNode -> TreeNode {
  ~parent
}

pred wellFormedTree[n: TreeNode] {
  // the sub-trees are not equal
  // some garantees non-emptiness
  some n.left or some n.right => left != right

  // no cycles in parent
  n not in n.^parent

  // every node has one parent except for root
  no root.n => one parent[n]

  let leftValues = { v: Int | v in n.left.(*children).value }, 
    rightValues = { v: Int | v in n.right.(*children).value }

  {
    // left side is smaller
    all lv: leftValues | lv < n.value 

    // right side is larger
    all rv: rightValues | n.value < rv

    // Difference of no nodes between left and right is less than 1
    (sub[#leftValues, #rightValues] <= 1)
  }

  // No two nodes have the same value
  all disj n, n': TreeNode | n.value != n'.value
}

pred show {
  one root
  all n: TreeNode | wellFormedTree[n]
}

run show for 1 Tree, exactly 7 TreeNode
