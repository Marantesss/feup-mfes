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

sig Color{}
sig Country {
  neighbors: set Country,
  color: Color
}
