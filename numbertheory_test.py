#!/usr/bin/env python3
'''%prog [options] <cmd>

Various discrete math, iterator, and set functions.

Copyright (C) Marty White 2011,2019 under the GNU GPL V3 or later.
'''


import sys, argparse, inspect, unittest

from numbertheory import *


class TestFact(unittest.TestCase):

  def test_fact(self):
    self.assertEqual( fact(0), 1 )
    self.assertEqual( fact(1), 1 )
    self.assertEqual( fact(2), 2 )
    self.assertEqual( fact(3), 6 )
    self.assertEqual( fact(5), 120 )
    self.assertEqual( fact(42), 1405006117752879898543142606244511569936384000000000 )

class TestNumPermComb(unittest.TestCase):

  def test_num_permuntations(self):
    self.assertEqual( numPermutations(5), 120 )
    for i in range(2, 12):
      self.assertEqual( numPermutations(i), fact(i) )
    self.assertEqual( numPermutations( 4, 2),  12 )
    self.assertEqual( numPermutations( 8, 3), 336 )

  def test_num_combinations(self):
    for c in (numCombinations, numCombinations_, nCr_):
      self.assertEqual( c( 4, 3),   4 )
      self.assertEqual( c( 5, 4),   5 )
      self.assertEqual( c( 8, 6),  28 )
      self.assertEqual( c( 8, 2),  28 )
      self.assertEqual( c(52, 5), 2598960 )

  def test_num_selections(self):
    self.assertEqual( numSelections(10, 3), 220 )
    self.assertEqual( numSelections(4, 12), 455 )

  def test_triangular(self):
    self.assertEqual( triangularNumber(4), 10 )
    for n in range(0, 30):
      self.assertEqual( triangularNumber(n), numCombinations(n+1, 2) )

class TestMisc(unittest.TestCase):

  def test_singleton(self):
    for item in (None, (), -2, -1, 0, 1, 2, .5, "c", "foo", [], [1, "list"], {}, {"answer":42}):
      self.assertEqual( singleton(item), (item,) )

  def test_iLen(self):
    self.assertEqual( iLen((7,8,9)), 3 )
    self.assertEqual( iLen([7,8,9]), 3 )
    self.assertEqual( iLen({"ham":3,"eggs":5,"answer":42}), 3 )
    self.assertEqual( iLen(range(42)), 42 )

  def test_asSequence(self):
    for q in ( (), [], (42,), [42], range(3), 'fubar', b'spam', {'ans':42} ):
      self.assertIs( asSequence(q), q )
    self.assertEqual( asSequence(i for i in 'ham'), ('h','a','m') )
    self.assertEqual( asSequence(i for i in 'ham' if i), ('h','a','m') )
    self.assertEqual( asSequence(zip('ham','egg')), (('h','e'),('a','g'),('m','g')) )
    self.assertEqual( sorted(asSequence(frozenset('ham'))), ['a','h','m'] )  # sorted() would convert any iterable to a list anyway
    s = asSequence(frozenset('ham'))
    self.assertTrue( isinstance(s, tuple) )
    self.assertTrue( len(s), 3 )
    self.assertTrue( all(item in 'ham' for item in s) )



class TestSubsets(unittest.TestCase):
  def test_unique(self):
    self.assertEqual( list(iUnique("fubarfubaz")), list("fubarz") )
  def test_subsets(self):
    self.assertEqual( list(iPowerSet([3,4,5])), [(),(3,),(4,),(4,3),(5,),(5,3),(5,4),(5,4,3)] )
    self.assertEqual( iLen(iPowerSet(range(10))), 1024 )
    self.assertEqual( list(iPowerSet("aab")), [(),('a',),('a',),('a','a'),('b',),('b','a'),('b','a'),('b','a','a')] )
    self.assertEqual( list(itertools.islice(iPowerSet(itertools.count()), 6)), [(),(0,),(1,),(1,0),(2,),(2,0)] )

    # sPowerSet

    self.assertEqual( list(iSubsetsK([3,4,5],2)), [(4,3),(5,3),(5,4)] )
    self.assertEqual( list(iSubsetsK(range(5),3)), [(2,1,0),(3,1,0),(3,2,0),(3,2,1)
                                                   ,(4,1,0),(4,2,0),(4,2,1),(4,3,0),(4,3,1),(4,3,2)] )
    self.assertEqual( list(itertools.islice(iSubsetsK(itertools.count(),2), 6))
                    , [(1,0),(2,0),(2,1),(3,0),(3,1),(3,2)] )
    self.assertEqual( sorted(sorted(s) for s in iSubsetsK(range(5),3)), sorted(sorted(s) for s in sSubsetsK(range(5),3)) )
 
    # sSubsetsK
    # iPairs_

    self.assertEqual( list(iPairs(range(4))), [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)] )
    self.assertEqual( list(sPairs(range(4))), [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)] )
    self.assertEqual( list(iTriples(range(4))), [(0,0,0),(1,0,0),(1,1,0),(1,1,1),
                                                 (2,0,0),(2,1,0),(2,1,1),(2,2,0),(2,2,1),(2,2,2),
                                                 (3,0,0),(3,1,0),(3,1,1),
                                                 (3,2,0),(3,2,1),(3,2,2),
                                                 (3,3,0),(3,3,1),(3,3,2),(3,3,3)
                                                ] )
    self.assertEqual( list(iTriples(range(4))), list(sTriples(range(4))) )
    # sTriples
    self.assertEqual( sorted(iPairs(range(10))),
                      sorted(iUnique(map(lambda ic: tuple(reversed(sorted(ic))), itertools.product(range(10),range(10)))))
                    )
    self.assertEqual( sorted(iPairs(range(10))), sorted(tuple(reversed(p)) for p in iPairs_(range(10))) )


class TestApply(unittest.TestCase):
  def test_apply(self):
    for f in (lambda n: n+1, lambda n: n*2, lambda n: n**2, fact):
      i = 3
      for j in RepeatApply(f, 3):
        self.assertEqual(i,j)
        i = f(i)
        if i > 1000:
          break

class TestItertools2(unittest.TestCase):
  def test_grouper(self):
    self.assertEqual( tuple(grouper('ABCDEFG', 3, 'x')),  (('A','B','C'),('D','E','F'),('G','x','x')) )
  def test_roundrobin(self):
    self.assertEqual( tuple(roundrobin('ABCD', 'EFGH', 'IJKL')), tuple('AEIBFJCGKDHL') )
    self.assertEqual( tuple(roundrobin('ABC',  'D'   , 'EF'  )), tuple('ADEBFC') )
 
  def test_transpose(self):
    self.assertEqual( list(transpose([1,2,3],[4,5,6])), [(1,4),(2,5),(3,6)] )

  def test_xselections(self):
    self.assertEqual( tuple(xselections((1,2,3,4), 2))
                    , ((1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3),(3,4),(4,1),(4,2),(4,3),(4,4))
                    )

  def test_odometer(self):
    self.assertEqual( tuple(itertools.islice(odometer(5),3)), ((0,0,0,0,0), (0,0,0,0,1), (0,0,0,0,2)) ) # up to 100000 and then rolling back around
    self.assertEqual( tuple(itertools.islice(odometer(5),99999,100002)), ((9,9,9,9,9), (0,0,0,0,0), (0,0,0,0,1)) )
    self.assertEqual( tuple(itertools.islice(odometer(2,"cab"),11))
                    , (('c','c'),('c','a'),('c','b'),('a','c'),('a','a'),('a','b'),('b','c'),('b','a'),('b','b'),('c','c'),('c','a'))
                    )

class TestIsHeapSubset(unittest.TestCase):
  def test_isHeapSubset(self):
    self.assertTrue(isHeapSubset('abc','abcde'))
    self.assertTrue(isHeapSubset('ace','abcde'))
    self.assertTrue(isHeapSubset('bc','abcde'))
    self.assertTrue(isHeapSubset('bd','abcde'))
    self.assertTrue(isHeapSubset('bcd','abcde'))
    self.assertTrue(isHeapSubset('cde','abcde'))
    self.assertFalse(isHeapSubset('abc','bcde'))
    self.assertFalse(isHeapSubset('cde','abcd'))

class TestAddends(unittest.TestCase):
  def test_addends(self):
    self.assertEqual( list(Addends(5)), [[5], [4,1], [3,2], [3,1,1], [2,2,1], [2,1,1,1], [1,1,1,1,1]] )

def CmdPermute(args):
  if len(args.W) == 1:
    items = args.W[0]
  else:
    items = args.W
  items = sorted(items)
  for p in itertools.permutations(items):
    print(' '.join(p))

def CmdAddends(args):
  for a in Addends(args.N): print(a)

def CmdUnitTest(args):
  unittest.main(argv=sys.argv[0:1])

def main(argv):

  ap = argparse.ArgumentParser( description = __doc__
                             #, epilog = epilog
                              , formatter_class = argparse.RawDescriptionHelpFormatter
                              )
  #ap.add_argument('cmd', nargs='?', default='unittest', help='unittest, permute, or addends')
  ap.set_defaults(cmdfn=CmdUnitTest)
  subparsers = ap.add_subparsers()

  unittest_parser = subparsers.add_parser('unittest')
  unittest_parser.set_defaults(cmdfn=CmdUnitTest)

  addends_parser = subparsers.add_parser('addends')
  addends_parser.add_argument('N', type=int)
  addends_parser.set_defaults(cmdfn=CmdAddends)

  permute_parser = subparsers.add_parser('permute')
  permute_parser.add_argument('W', nargs='+')
  permute_parser.set_defaults(cmdfn=CmdPermute)

  args = ap.parse_args(argv[1:])
  return args.cmdfn(args)

if __name__=='__main__':
  sys.exit(main(sys.argv))

