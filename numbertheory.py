#!/usr/bin/python3

# Copyright (C) Marty White 2011,2019 under the GNU GPL V3 or later.

import itertools, functools, operator, collections.abc

def fact(i):
  return functools.reduce(operator.mul, range(2,i+1), 1)

'''
Glossary:
  Set: an (unordered) collection of distinct objects.
  Subset: a set whose members are all also members of another set.
  Proper Subset: a subset of a larger set.
  Power Set: the set of all subsets of a given set.
  Cartesian Product: the set of all pairs of items from two sets (one from each).
  Permutations: distinct arrangements of a sequence.
    Example: anagrams
  Combinations: distinct subsets of a set, often k out of n items.  Order does not matter.
    Example: Good, Fast, Cheap: pick any two.  How many different pairs are there?
  Combinations With Repetition or k-combination or k-selection or k-multiset: combinations in which you can repeat your choices.
    Example: a combination lock has many possible combinations of numbers.  How many different 3-number combinations are possible?
    Example: words are combinations of letters.  How many different 4-letter words are possible?
  Selection: could be a Combination, or more likely a Combination With Repetition.
'''

def numPermutations(n, k=None):
  'Return the number of k-length arrangements of n items.'
  # Equal to n!/((n-k)!), but don't bother to multiply all the values that are inevitably going to be canceled out.
  if k is None: k = n
  return functools.reduce(operator.mul, range(n+1-k, n+1), 1)

def nCr_(n, r):
  'Number of combinations of n things taken r at a time'
  r = min(r, n-r)
  if r < 0: return 0
  numer = functools.reduce(operator.mul, range(n, n-r, -1), 1)
  denom = functools.reduce(operator.mul, range(1, r+1), 1)
  return numer // denom

def numCombinations_(n, k=None):
  'Return the number of possible k-length subsets from a set of n items.'
  if k is None: k = n
  return numPermutations(n,k) / fact(k)

def numCombinations(n, k=None):
    'Return the number of possible k-length subsets from a set of n items.'
    # This assumes no duplicate items.
    # Often notated with large parenthesis:
    # ( n )
    # ( k )
    # Or as C(n,k)
    # Equal to the Binomial Coefficient
    """
    A fast way to calculate binomial coefficients by Andrew Dalke (contrib).
    """
    if k is None: k = n
    if 0 <= k <= n:
        ntok = 1
        ktok = 1
        for t in range(1, min(k, n - k) + 1):
            ntok *= n
            ktok *= t
            n -= 1
        return ntok // ktok
    else:
        return 0

def numSelections(n,k=None):  # combinations with replacement
  'Return the number of combinations with repetition of k items from a repertoire of n items.'
  # Sometimes notated with large double-parenthesis:
  # (( n ))   ( n+k-1 )
  # (( k )) = (   k   )
  if k is None: k = n
  #return fact(n+k-1) / ( fact(n-1) * fact(k) )
  return numCombinations(n+k-1, k)

def triangularNumber(n):
  # Also equal to C(n+1, 2)
  return (n*(n+1))//2

def singleton(n):
  'Wrap anything inside a 1-tuple.'
  # Note that tuple(n) extracts the elements from any iterable, including strings.
  return (n,)

def iLen(iterable):
  return sum(1 for i in iterable)

def asSequence(iterable):
  "Convert an iterable into an indexable sequence if it isn't already."
  if isinstance(iterable, collections.abc.Sequence) or hasattr(iterable, '__getitem__'):
    return iterable
  else:
    return tuple(iterable)

# Nomenclature:
#   iNnn    iterator: consumes input & generates output as needed
#   sNnn    strict: consumes all input before generating any output

def iUnique(iterable, key=None):
  'Filter out duplicates from iterable.  Items must be hashable.'
  cache = set()
  cacheadd = cache.add
  if key is None:
    for i in iterable:
      if not i in cache:
        cacheadd(i)
        yield i
  else:
    for i in iterable:
      k = key(i)
      if not k in cache:
        cacheadd(k)
        yield i

def iPowerSet(iterable):
  '''Generate all subsets of iterable.
     Works on iterables of infinite length, though it does keep a copy of all output.
     Generates 2**len(iterable) subsets.
  '''
  yield ()
  prevOutput = [()]
  for e in iterable:
    moreOutput = []
    for es in prevOutput:
      subset = (e,)+es     # short_tuple + long_tuple ought to be better than long_tuple + short_tuple, sigh...
      yield subset
      moreOutput.append(subset)
    prevOutput += moreOutput

def sPowerSet(iterable):    # s stands for "strict" or "sequence"
  '''Generate all subsets of iterable.
     Consumes entire iterable before yielding any output.
     Much slower than iPowerSet()!
  '''
  indexable = asSequence(iterable)
  return ( tuple(indexable[i] for i in index_combo)
           for r in range(len(indexable)+1)
           for index_combo in itertools.combinations(range(len(indexable)),r) )

def iSubsetsK(iterable, k):
  '''Generate all k-length subsets of iterable more efficiently than just filtering iSubsets().
     Works on iterables of infinite length, though it does keep a copy of all output of length less than k.
     Generates n!/((n-k)!*k!) subsets.
  '''
  if k == 0:
    yield ()
    return
  prevOutput = [()]
  for e in iterable:
    moreOutput = []
    for es in prevOutput:
      n = len(es) + 1
      if n == k:
        yield (e,)+es
      elif n < k:
        moreOutput.append((e,)+es)
    prevOutput += moreOutput

def sSubsetsK(iterable, k):
  '''Generate all k-length subsets of iterable more efficiently than just filtering iPowerSet().
     Much slower than iSubsetsK()!
     Generates n!/((n-k)!*k!) subsets.
  '''
  indexable = asSequence(iterable)
  return ( tuple(indexable[i] for i in index_combo)
           for index_combo in itertools.combinations(range(len(indexable)),k) )

def iPairs(iterable):
  '''Return all unique combinations of 2 choices from iterable.
     Works on iterables of infinite length, though it does keep a copy of all input consumed.
  '''
  prior = []
  for i in iterable:
    prior.append(i)
    for j in prior:
      yield (i,j)

def iPairs_(iterable):
  return iUnique(map(lambda ic: tuple(sorted(ic)), itertools.product(iterable,iterable)))

def sPairs(iterable):
  '''Return all unique combinations of choices from iterable.
     sPairs([3,4,5]) == [(3,3),(4,3),(4,4),(5,3),(5,4),(5,5)]
     Much slower than iPairs()!
  '''
  indexable = asSequence(iterable)
  return ( (indexable[i], indexable[j]) for i in range(len(indexable))
                                        for j in range(i+1) )

def iTriples(iterable):
  'Return all unique combinations of 3 choices from iterable.'
  prior = []
  for item in iterable:
    prior.append(item)
    for j in range(len(prior)):
      for k in range(j+1):
        yield (item,prior[j],prior[k])

def sTriples(iterable):
  "Slower than iTriples()!"
  indexable = asSequence(iterable)
  return ( (indexable[i], indexable[j], indexable[k])
           for i in range(len(indexable))
           for j in range(i+1)
           for k in range(j+1) )

def RepeatApply(f, x):  # equivalent to Haskell's `iterate`
  '''Generate repeated applications of f to x:
       x, f(x), f(f(x)), ...
  '''
  yield x
  while True:
    x = f(x)
    yield x

# From itertools documentation
def grouper(iterable, n, fillvalue=None):
    "Collect data into fixed-length chunks or blocks"
    # grouper('ABCDEFG', 3, 'x') --> ABC DEF Gxx"
    args = [iter(iterable)] * n
    return itertools.zip_longest(*args, fillvalue=fillvalue)

# From itertools documentation
def roundrobin(*iterables):
    "roundrobin('ABC', 'D', 'EF') --> A D E B F C"
    # Recipe credited to George Sakkis
    pending = len(iterables)
    nexts = itertools.cycle(iter(it).__next__ for it in iterables)
    while pending:
        try:
            for next in nexts:
                yield next()
        except StopIteration:
            pending -= 1
            nexts = itertools.cycle(itertools.islice(nexts, pending))

def transpose(*args):
  return grouper(roundrobin(*args), len(args))

# From http://code.activestate.com/recipes/190465-generator-for-permutations-combinations-selections/ :
def xselections(items, n):
    if n==0: yield ()
    else:
        for i in range(len(items)):
            for ss in xselections(items, n-1):
                yield (items[i],)+ss

def odometer(width, values=(0,1,2,3,4,5,6,7,8,9)):
  'Endlessly generate tuples of combinations of values, like a car odometer.'
  #return itertools.cycle( itertools.product( *itertools.repeat(values, width) ) )  # cycle() saves entire cycle of values
  # repeat(my_iterator) keeps returning the same (soon exhausted) iterator.  [my_iterator for _ in iter(int,1)] works as desired.
  return itertools.chain.from_iterable( itertools.product( *itertools.repeat(values, width) ) for ever in iter(int,1) )

def isHeapSubset(xs, ys):
  '''Determine whether xs is a subset of ys, given that both sequences are sorted.'''
  # Worst case efficiency: O(xs+ys)
  # Typical efficiency is some fraction of the inputs.
  # Best case efficiency: O(1)
  # Use heapq.merge() to merge large pre-sorted sequences.
  #assert _BUGPRINT("xs = %r, ys = %r" % (xs,ys))
  i = 0                         # monotonically increasing index into ys
  for x in xs:                  # must find each of xs in ys
    while True:                 # keep searching ys for this x
      if i >= len(ys):
        return False            # ran out of ys
      y = ys[i]
      i += 1
      if x == y:
        break                   # found matching y, go to next x
      elif x < y:
        return False            # since ys are sorted, there must not be a matching y
  return True

def Addends(n, smallest=1, largest=None):
  "Addends(5) -> [5], [4,1], [3,2], [3,1,1], [2,2,1], [2,1,1,1], [1,1,1,1,1]"
  # The mathematics term for this is a "partition".
  if largest is None: largest = n
  if n <= largest:
    yield [n]
  for portion in range(smallest, 1+n-smallest):
    if n-portion <= largest:
      for subportion in Addends(portion, smallest=smallest, largest=n-portion):
        yield [n-portion]+subportion

