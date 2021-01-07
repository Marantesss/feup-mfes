/*
PART 1
------
1.  3
2.  4 (iden -> {(a,a), (b,b), (c,c), ...}, i.e no countries have themselves as neighbors)
3.  3
4.  3 (not sure)
5.  2 (check ... for is not valid)
    3 (same reason)
6.  3 (https://alloy.readthedocs.io/en/latest/language/sets-and-relations.html#relation-restriction)
7.  1
    2 (^R = {(a,b), (b,a), (b,c), (a,c), (a,a), (b,b)})
*/

-- Part 2
---------
open util/ordering[Placement]

-- 1
sig Place {}
sig Network {
  places: set Place,
  connections: places -> places
} {
  -- Connections are bidirectional: if there is a connection from X to Y, then there is
  -- also a connection from Y to X, i.e., the ‘connections’ relation is symmetric.
  connections = ~connections

  -- A place cannot be connected to itself, i.e., the 'connections' relation is anti-reflexive.
  no connections & iden

  -- The network must be connected, that is, there must exist a path between
  -- any two places in the network.
  all p1, p2: places | p2 in p1.*connections
}

-- 2
sig Object {}
sig Placement {
  network: Network,
  objects: set Object,
  -- positions relates objects with places, such that each object has exactly
  -- one place and each place has at most one object
  positions: objects lone -> one Place
} {
  -- The places where objects are positioned must belong to the network.
  objects.positions in network.places
}

-- 3
-- Moves an object o to an adjacent place p in a placement t,
-- resulting in a new placement t'.
pred moveObject[t: Placement, o: Object, p: Place, t': Placement] {
  -- Pre-conditions:
  -- the object (o) must exist in the initial placement (t)
  o in t.objects
  -- the target place (p) must be unnocupied in the initial placement (t)
  no t.positions.p
  -- the target place (p) must be adjacent to the initial place of the object (o)
  o.(t.positions) -> p in t.network.connections

  -- Post-conditions:
  -- (one per field of t’)
  t'.network = t.network
  t'.objects = t.objects
  t'.positions = t.positions ++ (o -> p) -- ++ because (o -> (o's old place) has to be removed from t.positions)
}

--- run moveObject for 7 but 1 Network, 1 Object

-- 4
fact {
  all t: Placement, t': t.next | some o: Object, p: Place | moveObject[t, o, p, t']
}

one sig x, y, z, w extends Place {}
one sig n extends Network {} {
  places = x + y + z + w
  connections = x->y + y->x + y->z + z->y + y->w + w->y
}
one sig a, b extends Object {}
one sig initial extends Placement {} {
  network = n
  objects = a + b
  positions = a->x + b->y
}

-- Swap objects in a minimal number of steps (6 moves, 7 Placements)
run success {
  first = initial and last.positions = a->y + b->x
} for 7 but exactly 1 Network, 2 Object, 4 Place

-- Trying to swap objects in fewer steps should fail
run failure {
  first = initial and last.positions = a->y + b->x
} for 6 but exactly 1 Network, 2 Object, 4 Place
