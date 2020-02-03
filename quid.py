#!/usr/bin/python3
'''%prog [options] <cmd>

Where <cmd> is one of:
  play [<number of players>]
  deal [[<number of hands>] <number of cards>]
  deck
  permute <cards>
  solve <cards>
  report

Copyright (C) Marty White 2011,2019-2020 under the GNU GPL V3 or later.'''

'''
To consider:
  * Package with base64-encoded lexicon wrapped inside a Python module:
      print('zlexocn="""%s"""' % base64.b64encode(zlib.compress(open('scrabble-words.txt').read(), 9)))
      lexicon = zlib.decompress(base64.b64decode(zlexicon))
  * improve AnagramSolver:
    - expand dictionaries when adding anything?
        ex: adding a new n-card hand
            -> all combinations with other n, n+2, n+3, ... -card hands
              -> which then generate their own combinations
            -> find all valid pairs of sub-hands: (2,n-2), (3,n-3), ...
    - cache results (possible with previous change)
    - cache results or generate complete solution to disk:
        dbm provides one table mapping from strings to strings:
          "c-a-r-d-s" -> "words;and;s-u-b,h-a-n-d-s"
        sqlite3 also maps scalars to scalars, but would enable also storing other tables:
           TABLE hands (hand TEXT, subhands TEXT)
           TABLE wordfreqs (word TEXT, uvalue FLOAT)
           TABLE letterfreqs (letters TEXT, uvalue FLOAT)
  * improve AI's basic decisions about cards to pick up & discard
  * enable AI to try to achive bonuses
  * enable user to choose difficulty level
  * enable different AI players with different strengths/weaknesses/personalities
  * enable AI & human users to challenge other players' words
    - enable AI to try to sneak non-words past player
  * enable human to enter name
  * enable multiple humans at terminal(s) / network
  * provide different decks: quiddler, scrable, bananagrams, quiddler-like but with natural letter frequency pair cards?
    - include extended deck
      2-tuples: he, th, in, er, ou, an, nd, it, at, re, ng, ha, on, to, ed, en, as, li, sh
      3-tuples: ing, the, thr, tri...?

Try:
  python -mtimeit '["fee", "fie", "fo", "fum"]'  # 0.171  usec
  python -mtimeit '("fee", "fie", "fo", "fum")'  # 0.0234 usec

'''

import sys, locale, codecs, optparse, os, unittest, inspect
import re, itertools, functools, random, operator, collections, heapq, sqlite3
import numbertheory as NTH

_DEBUG = 0

def _BUGEXEC(stmt, debug=1, locals=None):
  '''  `python -O` will delete assert statements.
        To enable debugging code to be optimized away completely,
          call it from an assert statement:
            assert _BUGEXEC("print(f())")
  '''
  if _DEBUG >= debug:
    if locals is None:
      exec(stmt)
    else:
      exec(stmt, globals(), locals)
  return True

def _BUGPRINT(s, debug=1):
  '''Use `assert _BUGPRINT("%f"%n)` to enable complete optimization.'''
  if _DEBUG >= debug: print(s)
  return True

#VALID_WORDS_FILE = '/usr/share/dict/words'
#VALID_WORDS_FILE = 'scrabble-words.txt'
VALID_WORDS_FILE = 'scrabble-word-counts.txt'

# Scrabble, Bananagrams, and Quiddler stats

S_FREQS_ = \
  { 'a' :  9
  , 'b' :  2
  , 'c' :  2
  , 'd' :  4
  , 'e' : 12
  , 'f' :  2
  , 'g' :  3
  , 'h' :  2
  , 'i' :  9
  , 'j' :  1
  , 'k' :  1
  , 'l' :  4
  , 'm' :  2
  , 'n' :  6
  , 'o' :  8
  , 'p' :  2
  , 'q' :  1
  , 'r' :  6
  , 's' :  4
  , 't' :  6
  , 'u' :  4
  , 'v' :  2
  , 'w' :  2
  , 'x' :  1
  , 'y' :  2
  , 'z' :  1
  }

S_POINTS_ = \
  { 'a' :  1
  , 'b' :  3
  , 'c' :  3
  , 'd' :  2
  , 'e' :  1
  , 'f' :  4
  , 'g' :  2
  , 'h' :  4
  , 'i' :  1
  , 'j' :  8
  , 'k' :  5
  , 'l' :  1
  , 'm' :  3
  , 'n' :  1
  , 'o' :  1
  , 'p' :  3
  , 'q' : 10
  , 'r' :  1
  , 's' :  1
  , 't' :  1
  , 'u' :  1
  , 'v' :  4
  , 'w' :  4
  , 'x' :  8
  , 'y' :  4
  , 'z' : 10
  }

B_FREQS_ = \
  { 'a' : 13
  , 'b' :  3
  , 'c' :  3
  , 'd' :  6
  , 'e' : 18
  , 'f' :  3
  , 'g' :  4
  , 'h' :  3
  , 'i' : 12
  , 'j' :  2
  , 'k' :  2
  , 'l' :  5
  , 'm' :  3
  , 'n' :  8
  , 'o' : 11
  , 'p' :  3
  , 'q' :  2
  , 'r' :  9
  , 's' :  6
  , 't' :  9
  , 'u' :  6
  , 'v' :  3
  , 'w' :  3
  , 'x' :  2
  , 'y' :  3
  , 'z' :  2
  }

Q_FREQS_ = \
  { 'a' : 10
  , 'b' :  2
  , 'c' :  2
  , 'd' :  4
  , 'e' : 12
  , 'f' :  2
  , 'g' :  4
  , 'h' :  2
  , 'i' :  8
  , 'j' :  2
  , 'k' :  2
  , 'l' :  4
  , 'm' :  2
  , 'n' :  6
  , 'o' :  8
  , 'p' :  2
  , 'q' :  2
  , 'r' :  6
  , 's' :  4
  , 't' :  6
  , 'u' :  6
  , 'v' :  2
  , 'w' :  2
  , 'x' :  2
  , 'y' :  4
  , 'z' :  2
  , 'cl' : 2
  , 'er' : 2
  , 'in' : 2
  , 'qu' : 2
  , 'th' : 2
  }

Q_POINTS_ = \
  { 'a' :  2
  , 'b' :  8
  , 'c' :  8
  , 'd' :  5
  , 'e' :  2
  , 'f' :  6
  , 'g' :  6
  , 'h' :  7
  , 'i' :  2
  , 'j' : 13
  , 'k' :  8
  , 'l' :  3
  , 'm' :  5
  , 'n' :  5
  , 'o' :  2
  , 'p' :  6
  , 'q' : 15
  , 'r' :  5
  , 's' :  3
  , 't' :  3
  , 'u' :  4
  , 'v' : 11
  , 'w' : 10
  , 'x' : 12
  , 'y' :  4
  , 'z' : 14
  , 'cl' : 10
  , 'er' :  7
  , 'in' :  7
  , 'qu' :  9
  , 'th' :  9
  }

# According to Google/Norvig circa 2012
# http://norvig.com/mayzner.html
G_FREQS_ = \
  { 'e' : 445200000000
  , 't' : 330500000000
  , 'a' : 286500000000
  , 'o' : 272300000000
  , 'i' : 269700000000
  , 'n' : 257800000000
  , 's' : 232100000000
  , 'r' : 223800000000
  , 'h' : 180100000000
  , 'l' : 145000000000
  , 'd' : 136000000000
  , 'c' : 119200000000
  , 'u' :  97300000000
  , 'm' :  89500000000
  , 'f' :  85600000000
  , 'p' :  76100000000
  , 'g' :  66600000000
  , 'w' :  59700000000
  , 'y' :  59300000000
  , 'b' :  52900000000
  , 'v' :  37500000000
  , 'k' :  19300000000
  , 'x' :   8400000000
  , 'j' :   5700000000
  , 'q' :   4300000000
  , 'z' :   3200000000
  }
  
G_PAIR_FREQS_ = \
  { 'th' : 100272945963 # rank 1
  , 'he' : 86697336727
  , 'in' : 68595215308
  , 'er' : 57754162106
  , 'an' : 55974567611
  , 're' : 52285662239
  , 'on' : 49570981965
  , 'at' : 41920838452
  , 'en' : 41004903554
  , 'nd' : 38129777631  # rank 10
  , 'ng' : 26871805511  # rank 24
  , 've' : 23270129573  # rank 31
  , 'ch' : 16854985236  # rank 44
  , 'ex' : 6035335807   # rank 127
  , 'ke' : 6027536039   # rank 128
  , 'cl' : 4201617719   # rank 159
  , 'qu' : 4160167957   # rank 162
  , 'iz' : 1814164135   # rank 233
  , 'ju' : 1655210582   # rank 240
  # Not on the list at all: jq, qg, qk, qy, qz, wq, wz
  }

G_TOTAL_LETTERS_ = 3563505777820
G_TOTAL_BIGRAMS_ = 2800000000000  # approx

# There probably is/should be a formula for the value of a
# pair-of-a-certain-frequency vs the value of its constituent
# letters-of-certain-frequencies.
# Draft suggestion for other pair values:
G_POINTS_ = \
  { 'th' : 9    # t+h-1
  , 'he' : 8
  , 'in' : 7    # i+n
  , 'er' : 7    # e+r
  , 'an' : 7
  , 're' : 7
  , 'on' : 7
  , 'at' : 5
  , 'en' : 7
  , 'nd' : 9
  , 'ng' : 10
  , 've' : 12
  , 'ch' : 12
  , 'ex' : 10
  , 'ke' : 10
  , 'cl' : 10   # c+l-1
  , 'qu' : 9    # (q+u)*.47
  , 'iz' : 15
  , 'ju' : 13
  , 'q'  : 14
  , 'z'  : 15
  }

class TestQ(unittest.TestCase):
  # Basic sanity tests of above data
  def test_q(self):
    self.assertEqual( len(Q_POINTS_), len(Q_FREQS_) )
    self.assertEqual( set(Q_POINTS_.keys()), set(Q_FREQS_.keys()) )
  def test_s(self):
    self.assertEqual( len(S_POINTS_), len(S_FREQS_) )
    self.assertEqual( set(S_POINTS_.keys()), set(S_FREQS_.keys()) )

class Cards(list):
  # A list of cards that can shuffle and score itself.

  def __init__(self, aList=None):
    if aList is None:
      aList = []
    list.__init__(self, aList)

  @staticmethod
  def FullDeck():
    return Cards(a for a in Q_FREQS_ for i in range(Q_FREQS_[a]))
    #assert len(Cards.FullDeck()) == 118

  def TotalPoints(self):
    return sum(Q_POINTS_[c] for c in self)

  def AveragePoints(self):
    if len(self):
      return self.TotalPoints() / len(self)
    else:
      return None

  def SortedByPoints(self):
    return Cards(sorted(self, key = lambda c: (Q_POINTS_[c], c)))

  def Shuffle(self):
    random.shuffle(self)

  def Pop(self, n=1):
    assert n > 0
    popped = Cards(self[-n:])
    del self[-n:]
    return popped

  def Peek(self, n=1):
    assert n > 0
    return Cards(self[-n:])

  def Push(self, cards):
    #self[0:0] = cards
    self.extend(cards)

class TestCards(unittest.TestCase):
  def test_cards(self):
    cs = Cards([3,4,5])
    cs.Push([6,7])
    self.assertEqual( cs, [3,4,5,6,7] )
    self.assertEqual( cs.Pop(3), [5,6,7] )
    self.assertEqual( cs, [3,4] )

def ReportDeck():
  deck = Cards.FullDeck().SortedByPoints()
  print("deck, sorted by points:", [(c, Q_POINTS_[c]) for c in deck])
  print("average card points:", deck.AveragePoints())
  print("median card:", deck.SortedByPoints()[int(len(deck)/2)])
  # print "number of possible hands:"
  # TODO: turns out this is deplorably hard to calculate

def ReportLexicon(lexicon):
  print("Scanning lexicon (%d words)..." % len(lexicon))
  # TODO: return metrics for hands of size 3..10 plus unlimited
  # Metrics (for all words, for words with 10 or fewer cards):
  #   word with most cards
  #   word with highest score
  #   word with most 2-letter cards
  #   longest word with only 2-letter cards
  deck = Cards.FullDeck()
  def most_tuples(cs):
    for c in cs:
      if len(c) <= 1:
        return 0
    return len(cs)
  def most_valuable_tuples(cs):
    for c in cs:
      if len(c) <= 1:
        return 0
    return TotalCardPoints(cs)
  metrics = { "most cards"   : len
            , "most letters" : lambda cs: len(''.join(cs))
            , "most points"  : TotalCardPoints
            , "most cards without 1-letter cards": most_tuples
            , "most points without 1-letter cards": most_valuable_tuples
            }
  measures = [ {} for i in range(16) ]
  no_deck = set()
  no_hand = set()
  for word in sorted(lexicon):
    nMatches = 0
    for (match,), remainder, unmatched in HandMatch(deck, word, permissive=False):
      nMatches += 1
      if len(match) > 10:
        no_hand.add(word)
      for k,f in metrics.items():
        value = f(match)
        for i in range(len(match), len(measures)):
          v,m = measures[i].get(k, (0,set()))
          if value > v:
            m = set()
          if value >= v:
            m.add(match)
            measures[i][k] = (value, m)
            #if value> 0: print(k, value, '-'.join(match))
    if nMatches == 0:
      no_deck.add(word)
  for i in range(3,len(measures)):
    print("\nFor a maximum of %d cards:" % i)
    for k in sorted(measures[i].keys()):
      (v,ms) = measures[i][k]
      print("  %s: %d  (%d matches)" % (k, v, len(ms)))
      if len(ms) <= 64:
        print("   ","\n    ".join('-'.join(m) for m in sorted(ms)))
  print()
  print("\n  ".join( ["%d words matchable by deck but requiring more than 10 cards:" % len(no_hand)]
                   + sorted(no_hand,key=lambda w: (len(w),w))
                   ))
  print()
  print("\n  ".join( ["%d words not matchable by deck:" % len(no_deck)]
                   + sorted(no_deck, key=lambda w: (len(w),w))
                   ))
  # Key results:
  #   For a maximum of 10 cards:
  #     most letters: 14: cl-a-p-p-er-cl-a-w-in-g u-n-d-er-cl-o-th-in-g-s
  #     most points: 71: b-u-m-f-u-z-z-l-in-g w-h-i-z-z-b-a-n-g-s
  #     most cards without 1-letter cards: 4: in-cl-in-er
  #     most points without 1-letter cards: 31: in-cl-in-er
  #   For any length hand:
  #     most letters: 15
  #     most points: 83: s-u-b-j-e-c-t-i-v-i-z-i-n-g s-u-b-j-e-c-t-i-v-i-z-in-g
  #     most cards without 1-letter cards: 4: in-cl-in-er
  #     most points without 1-letter cards: 31: in-cl-in-er
  #     most cards: 15:


def Report(lexicon):
  ReportDeck()
  print()
  ReportLexicon(lexicon)

def ReportVowelConsonantStats(lexicon):
  measures = [ {"nWords":0, "nConsonants":0, "fWords":0, "fConsonants":0} for i in range(50) ]
  xlateNoVowels = str.maketrans("", "", "aeiouyAEIOUY")
  for word in lexicon:
    if word.isalpha():
      i = len(word)
      nConsonants = len(word.translate(xlateNoVowels))
      measures[i]["nConsonants"] += nConsonants
      measures[i]["nWords"] += 1
      measures[i]["fConsonants"] += nConsonants * lexicon[word]
      measures[i]["fWords"] += lexicon[word]
  print("Of the words in the lexicon, and taking Y to be a vowel:")
  for i in range(50):
    if measures[i]["nWords"] > 0:
      nWords = float(measures[i]["nWords"])
      print("%6d words with %2d letters: %.2f (%.2f%%) consonants / %.2f (%.2f%%) vowels" % \
      ( measures[i]["nWords"]
      , i
      , measures[i]["nConsonants"] / nWords
      , (measures[i]["nConsonants"] / nWords) / i
      , i - measures[i]["nConsonants"] / nWords
      , (i - measures[i]["nConsonants"] / nWords) / i
      ))
  print('Taking frequency of word usage into account ("the" counts much more than "thy"):')
  for i in range(50):
    if measures[i]["nWords"] > 0:
      nWords = float(measures[i]["fWords"])
      print("%6d words with %2d letters: %.2f (%.2f%%) consonants / %.2f (%.2f%%) vowels" % \
      ( measures[i]["nWords"]
      , i
      , measures[i]["fConsonants"] / nWords
      , (measures[i]["fConsonants"] / nWords) / i
      , i - measures[i]["fConsonants"] / nWords
      , (i - measures[i]["fConsonants"] / nWords) / i
      ))


common_suffixes = "s es ed er ers ies ing".split()

def withoutCommonSuffix(word):
  # Return the given word, removing a common suffix it may have had.
  for suffix in common_suffixes:
    xn = len(suffix)
    if word[-xn:] == suffix:
      return word[:-xn]
  return word

def ReportShortList(lexicon):
  'Generate various lists of interesting words.'
  # Generate a set of patterns to match interesting words:
  #   words that are short and have valuable cards

  deck = Cards.FullDeck()
  ntokens = float(sum(lexicon.values()))
  max_uvalue = 5e-4  # don't list the most common couple hundred words

  some_words = set()
  short_lexicon = {}
  for word in lexicon:
    u = lexicon[word]/ntokens
    found_match = False
    if u <= max_uvalue and len(word) <= 14: # can't form words longer than 14 letters from 10 Quiddler cards
      # Can this word be made using cards from the deck?
      for (match,), remainder, unmatched in HandMatch(deck, word, False):
        if len(match) <= 10:
          found_match = True
        break # only need 0 or 1 matches
    if found_match:
      short_lexicon[word] = u
    elif len(word) <= 5 and u >= max_uvalue:
      some_words.add(word)
  print('<tr class="notshort"><td>common short words</td><td>')
  #print(' '.join(sorted(some_words, key=lambda s: (len(s),s))))
  print(' '.join(sorted(some_words)))
  print('</td></tr>')

  max_letters = 8
  important_cards = [ c for c in Q_POINTS_ if Q_POINTS_[c] >= 7 or c=='y' ]   # b, c, cl, er, ...
  important_cards.sort()
  all_found = set()
  for c in important_cards:
    if c == 'q':
      cq = r'q(?!u)'   # remove *qu* words from *q* list
    else:
      cq = c
    patterns = [ '^%s%s%s$' % ('.'*i, cq, '.'*(n-i))       # n-letter words with c in them
                 for n in range(1, max_letters+1-len(c))
                 for i in range(n+1) ]
    #print patterns
    rexps = [ re.compile(p) for p in patterns ]
    word_sets = [ set() for i in range(max_letters+1) ]
    for word in short_lexicon:
      if len(word) <= max_letters:
        for x in rexps:
          m = x.search(word)
          if not m is None:
            skip = False
            if len(word) > 3:
              root = withoutCommonSuffix(word)
              if root != word and root in word_sets[len(root)]:
                #print("skipping", word)
                skip = True
                break
            if not skip:
              word_sets[len(word)].add(word)
            break
    some_words = set()
    for ws in word_sets:
      if len(' '.join(some_words|ws)) < 1040: # arbitrary cut-off number of chars per category
        some_words.update(ws)
        all_found.update(ws)
    #some_words_sorted = sorted(some_words, key=lambda s: (len(s),s))
    some_words_sorted = sorted(some_words)
    print('<tr><td>%s<span class="points">%s</span></td><td>\n%s\n</td></tr>' % \
      (c, Q_POINTS_[c], ' '.join(some_words_sorted)))
  #for w in sorted(all_found):(print w)

  # Report words with lots of vowels or consonants.
  re_vowel = re.compile(r'[aeiou]')
  re_consonant = re.compile(r'[bcdfghjklmnpqrstvwxz]')
  vcratios = set()
  for word in short_lexicon:
    (wd, num_consonants) = re_consonant.subn('', word)
    (_,  num_vowels) = re_vowel.subn('', wd)
    n = float(len(word))
    assert num_consonants <= n and num_vowels <= n
    vcratios.add( (num_vowels/n, num_consonants/n, word) )
  min_ratio_consonants = 6/7.0
  min_ratio_vowels = 2/3.0
  max_letters = 7
  ge = '&ge;' # or '&#x2265;' or '&#8805;' or '\u2265'
  print('<tr><td>consonants<br>%s %d%%</td><td>' % (ge, min_ratio_consonants*100))
  some_words = set()
  for (_,c,w) in sorted(vcratios, key=lambda v__c__w_: (1-v__c__w_[1], len(v__c__w_[2]), v__c__w_[2])):
    assert c <= 1.0
    if c >= min_ratio_consonants and len(w) <= max_letters and not withoutCommonSuffix(w) in some_words:
      some_words.add(w)
    elif c < 0.8:
      assert c < min_ratio_consonants
      break
  print(' '.join(sorted(some_words)))
  print('</td></tr>')
  print('<tr><td>vowels<br>%s %d%%</td><td>' % (ge, min_ratio_vowels*100))
  some_words = set()
  for (v,_,w) in sorted(vcratios, key=lambda v__c__w_1: (1-v__c__w_1[0], len(v__c__w_1[2]), v__c__w_1[2])):
    assert v <= 1.0
    if v > min_ratio_vowels and len(w) <= max_letters and not withoutCommonSuffix(w) in some_words:
      some_words.add(w)
    elif v < 0.6:
      assert v < min_ratio_vowels
      break
  print(' '.join(sorted(some_words)))
  print('</td></tr>')

class Incrementer(object):
  # For use in outputting progress.
  def __init__(self, start=0):
    self._value = start
  def inc(self):
    self._value += 1
    return self._value
  def add(self, n):
    self._value += n
    return self._value
  def value(self):
    return self._value

# These deep-object-iterators are terribly slow.

def ExtremeIter_NOT_USED(obj):
  # A crude attempt to iterate all the sub-objects.
  stash = [obj]
  while len(stash):
    obj = stash[0]
    yield obj
    try:
      it = iter(obj)
    except TypeError:
      it = None
    if not it is None:
      for obj in it:
        if not obj in stash:
          stash.append(obj)
    del stash[0]

def DeepIter(obj):
  # Iterate all the objects inside the given object.
  # Probably not a good idea.
  def inside(s, x):
    try:
      return x in s
    except TypeError:
      return False
  seen_list = [None]
  seen_set = set()
  found_list = [obj]
  while len(found_list):
    obj = found_list.pop()
    if inside(seen_set, obj) or obj in seen_list:
      continue
    yield obj
    if isinstance(obj, str):
      it = None
    elif isinstance(obj, dict):
      it = iter(obj.items())
    elif isinstance(obj, (tuple, list, set)):
      try:
        it = iter(obj)
      except TypeError:
        it = None
    if not (inside(seen_set, it) or it in seen_list):
      try:
        seen_set.add(it)
      except TypeError:
        seen_list.append(it)
      for obj in it:
        if not (inside(seen_set, obj) or obj in seen_list or obj in found_list):
          found_list.append(obj)

def DeepSizeOf(obj):
  # Attempt to report how much memory is used by the given object.
  return sum(sys.getsizeof(it) for it in DeepIter(obj))

def HandMatch(hand, word, permissive=True):
  ''' Match a hand of cards to a string of characters in all possible ways.
      Input is a collection of cards and a string.
        Generates tuples of
        ( tuples_of_matching_sequences, remaining_items_from_hand, unmatched_items_in_word ).
      If permissive is False,
        require all characters in word to be matched exactly.
      Else,
        Allow hyphens to separate letters without breaking words,
        Any unmatched character other than a hyphen or a space is added to the
          tuple of unmatched items and interpreted as a word break.
  '''
  assert _BUGPRINT("HandMatch(%s, %s, %s)" % (repr(hand), repr(word), repr(permissive)), debug=2 )
  assert isinstance(word, str)
  #original_hand = multiset.multiset(hand)
  original_hand = collections.Counter(hand)
  stack = []
  stack.append( (hand, word, ((),), ()) )  # (remaining input cards, remaining input string, parsed words, unmatched)
  while stack:
    hand, word, parse, unmatched = stack.pop()
    found = False
    for z in [1,2]:
      c = word[:z]
      if len(c) == z and c in hand:
        found = True
        subparse = parse[:-1] + (parse[-1] + (c,),)  # append to last parsed word
        subhand = list(hand)
        subhand.remove(c)  # removes first occurence
        if len(word) <= z:
          #  subparse: tuple of tuples of strings
          #  subhand: tuple of strings
          #assert multiset.multiset(itertools.chain.from_iterable(subparse + (subhand,))) == original_hand
          assert collections.Counter(itertools.chain.from_iterable(subparse + (subhand,))) == original_hand
          yield subparse, tuple(subhand), unmatched
        else:
          stack.append( (subhand, word[z:], subparse, unmatched) )
    if permissive and not found:
      if len(word):
        if not (word.startswith('-') or word.startswith('_')):
          if parse[-1] != ():
            parse = parse + ((),)  # start new word
        if not word[0] in ' -_':
          unmatched += (word[0],)
        stack.append( (hand, word[1:], parse, unmatched) )
      else:
        if parse[-1] == ():
          parse = parse[:-1]
        yield parse, tuple(hand), unmatched

def HandMatch0(hand, word):
  "Generate unique combinations of cards (items from hand) that can form the given word (sequence)."
  assert _BUGPRINT("HandMatch0(%s, %s)" % (repr(hand), repr(word)), debug=2)
  assert isinstance(word, str)
  for z in [1,2]:  # for each possible match length in range(min(map(len,hand)),1+max(map(len,hand)))
    c = word[:z]
    assert _BUGPRINT( '  '+repr(c), debug=3 )
    if len(c) == z and c in hand:  # if word[:1]==('a',), then not ('a',) in ('a',)
      if len(word) <= z:
        yield (c,)
      else:
        subhand = list(hand)
        subhand.remove(c)
        for m in HandMatch0(subhand, word[z:]):
          yield (c,) + m
#HandMatch1 = lambda h,w: itertools.imap(lambda w: ((w,),(),()), HandMatch0(h,w,False))
#HandMatch0 = lambda h,w: itertools.imap(lambda t: tuple(itertools.chain(*t[0])), HandMatch(h,w,False))

class TestMatchers(unittest.TestCase):
  def test_handmatch(self):
    self.assertEqual( list(HandMatch( ['t','h','e'], "the" )), [((('t','h','e'),),(),())] )
    self.assertEqual( list(HandMatch( ['th','e'   ], "the" )), [((('th','e'   ),),(),())] )
    self.assertEqual( sorted(HandMatch(['th','t','h','e'], "the" )),
                      [ ((('t','h','e'   ),),('th',  ),())
                      , ((('th','e'      ),),('t','h'),())
                      ])
    self.assertEqual( list(HandMatch(['th','t','h','e'], "t-he" )), [ ((('t','h','e'   ),),('th',  ),()) ])
    self.assertEqual( list(HandMatch(['th','t','h','e'], "t_he" )), [ ((('t','h','e'   ),),('th',  ),()) ])
    self.assertEqual( list(HandMatch(['th','t','h','e'], "t he" )), [ ((('t',),('h','e' )),('th',  ),()) ])
    self.assertEqual( list(HandMatch(['t','h','e'], "txhe" )), [ ((('t',),('h','e')),(),('x',)) ] )
    self.assertEqual( list(HandMatch(['a','b','c'], "xyz")), [ ((),('a','b','c'),('x','y','z')) ] )
    self.assertEqual( list(HandMatch(['a','b','c'], "abb")), [ ((('a','b'),),('c',),('b',)) ] )
    self.assertEqual( list(HandMatch(['a','a','b','c'], "abc")), [ ((('a','b','c'),),('a',),()) ] )
    self.assertEqual( list(HandMatch(['a','i','r','s','t'], "stair")) , [ ((('s','t','a','i','r'),), (), ()) ] )
    self.assertEqual( list(HandMatch(['a','a','b','b'], "bbaa")), [ ((('b','b','a','a'),),(),()) ] )
    self.assertEqual( list(HandMatch(['a','b','c','a','b','c'], "caabb")), [ ((('c','a','a','b','b'),),('c',),()) ] )
    self.assertEqual( list(HandMatch(['a','b','c','a','b','c'], "abcabc")), [ ((('a','b','c','a','b','c'),),(),()) ] )

    # This checks that the hand is not re-ordered, and that matches are pulled from the left.
    self.assertEqual( list(HandMatch(['b','a','c','a'], "a")), [ ((('a',),), ('b','c','a'), ()) ] )

    self.assertEqual( list(HandMatch(['t','h','e'], "the",  permissive=False )), [ ((('t','h','e'),),(),()) ] )
   #self.assertEqual( list(HandMatch(['t','h','e'], "txhe", permissive=False )), [ (((),),('t','h','e'),()) ] )
    self.assertEqual( list(HandMatch(['t','h','e'], "txhe", permissive=False )), [ ] )

  def test_alloc(self):
    self.assertEqual( list(HandMatch0(['t','h','e'], "the")) , [('t','h','e')] )
    self.assertEqual( list(HandMatch0(['th','e'   ], "the")) , [('th','e'   )] )
    self.assertEqual( NTH.iLen(HandMatch0(['th','t','h','e'   ], "the"  )) , 2 )
    self.assertEqual( NTH.iLen(HandMatch0(['a','b','c'        ], "x"    )) , 0 )
    self.assertEqual( NTH.iLen(HandMatch0(['a','b','c'        ], "abb"  )) , 0 )
    self.assertEqual( NTH.iLen(HandMatch0(['a','a','b','c'    ], "abc"  )) , 1 )
    self.assertEqual( NTH.iLen(HandMatch0(['a','i','r','s','t'], "stair")) , 1 )
    self.assertEqual( NTH.iLen(HandMatch0(['a','a','b','b'    ], "bbaa" )) , 1 )
    self.assertEqual( NTH.iLen(HandMatch0(['a','a','b','b','c'], "caabb")) , 1 )
    self.assertEqual( NTH.iLen(HandMatch0(['a','b','c','a','b','c'], "abcabc")) , 1 )
    #self.assertEqual( NTH.iLen(HandMatch0(['a','b','c','a','b','c'], tuple("abcabc"))) , 1 )
    #self.assertEqual( NTH.iLen(HandMatch0(['a','b','c','a','b','c'], list("abcabc"))) , 1 )

def TotalCardPoints(cards):
  return sum(Q_POINTS_[c] for c in cards)

def TotalWordPoints(words):
  total = 0
  for w in words:
    pts = sum(Q_POINTS_[c] for c in w)
    if len(w) > 1:
      total += pts
    else:
      total -= pts
  return max(0, total)

def SolveSlow(lexicon, args):
  "Given a list of cards, find valid words."
  # Solve by permuting the ordering and grouping of cards and
  #   seeing if that matches up with dictionary words.
  hand = sorted(args)
  words = set(lexicon)
  solutions = set()
  partitions = list(NTH.Addends(len(hand)))
  for p in itertools.permutations(hand):
    for lengths in partitions:
      subwords = []
      used = []
      unused = []
      i = 0
      for n in lengths:
        candidate = p[i:i+n]
        if ''.join(candidate) in words:
          subwords.append('-'.join(candidate))
          used.extend(candidate)
        else:
          unused.extend(candidate)
        i += n
      if subwords != []:
        subwords = tuple(sorted(subwords))
        unused = tuple(sorted(unused))
        value = TotalCardPoints(used) - TotalCardPoints(unused)
        if not (value,subwords,unused) in solutions:
          assert _BUGPRINT( ' '.join(subwords) + '/' + ' '.join(unused), debug=2 )
          solutions.add((value,subwords,unused))
  solutions = list(solutions)
  solutions.append( (-TotalCardPoints(hand), (), tuple(hand)) )
  solutions.sort()
  for (value,used,unused) in solutions:
    print("% 4d:  %s  /  %s" % (value, '  '.join(used), '  '.join(unused)))

class TestSlowSolve(unittest.TestCase):
  def test_solve(self):
    pass
    # Test case: b g h i i j k th w -> jib whig k th
    #   initial run: 128 seconds
    #   cache output of addends() in partitions: 43 seconds (nearly 3x faster!)
    # Test case 2: b g h i i j k m th w -> hm jib with g k, 42 points, 681 seconds
    # Test case 3: a t m e i n o r u s
    # Test case 4: a a a n n n t t t -> ant ant tan

def LoadLexicon(filename=VALID_WORDS_FILE):
  # Load a list of words
  assert _BUGPRINT( "LoadLexicon(%r)" % filename )
  xs = []
  for word in open(filename):
    word = word[:-1] # chomp newline
    if word.isalpha() and word.islower() and len(word) > 1:
      xs.append(word)
  return xs

def LoadLexiconF(filename):
  # Load a list of words and their usage counts:
  #   the 290770286    # 'the' is used 290770286 times in some corpus
  assert _BUGPRINT( "LoadLexiconF(%r)" % filename )
  x = {}
  for line in open(filename):
    word, count = line.split()
    if word.isalpha() and word.islower() and len(word) > 1 and count.isdigit():
      x[word] = int(count)
  return x

class AnagramDictionary(object):

  '''
  An AnagramDictionary is a mapping from combinations of cards to valid sets of words.
  Externally, the user provides a lexicon and requests anagrams.
  Internally:
    key - sorted tuple of cards
    value - set of all valid words (card orderings) and valid pairs of sub-hands
              that can be formed from the key.
  Starting with valid 1-word solutions for the given bunch of cards,
    combine all valid pairs of solutions into larger valid solutions.
    When done, the given hand and all its subhands will be fully factored.
    Solutions can then be recursively generated with minimal inefficiency.
  To most efficiently solve all possible hands, add the entire deck at once.
  To least efficiently solve multiple hands, add them one at a time.
  '''

  class Word(tuple): __slots__ = ()  # sys.getsizeof(Word((x,y))) == sys.getsizeof(tuple((x,y)))
  class Pair(tuple): __slots__ = ()

  min_cards = 2
  max_chars_per_card = 2

  def __init__(self, lexicon, max_cards=10, solutions_database=None):
    self.lexicon = lexicon
    self.max_cards = max_cards  # no full solutions will be generated larger than this
    assert _BUGPRINT("AnagramDictionary(lexicon=#%d, max_cards=%d)" % (len(lexicon),self.max_cards))
    assert self.max_cards >= self.min_cards
    self.combo_caches = [collections.defaultdict(set) for i in range(self.max_cards+1)]
    # combo_caches is:
    # a list, indexed by number of cards
    #     [ {}
    #     , {}
    #     , TWO_CARD_SOLUTION_SETS
    #     , THREE_CARD_SOLUTION_SETS
    #     , FOUR_CARD_SOLUTION_SETS
    #     , {('a','i','r','s','t'):set([Pair((('a','t'),('i','r','s'))),Word(('s','t','a','i','r'))])}
    #     ]
    # of mappings of a sorted tuple of cards
    #     { FIVE_CARD_HAND : SET_OF_SOLUTIONS }
    #     { ('a','i','r','s','t') : set([Pair((('a','t'),('i','r','s'))),Word(('s','t','a','i','r'))]) }
    # to sets
    #     set([ SOLUTION1, SOLUTION2, SOLUTION3, ... ])
    #     set([ Pair((('a','t'),('i','r','s'))), Word(('s','t','a','i','r')) ])
    # of legal words (sequences) that the cards can form,
    #     Word( (CARD1, CARD2, CARD3, CARD4, CARD5) )
    #     Word( ('s','t','a','i','r') )
    # or pairs of hands that themselves form one or more legal words.
    #     Pair( (TWO_CARD_HAND,THREE_CARD_HAND) )
    #     Pair( (('a','t'),('i','r','s')) )
    self.db = None
    self.dbcursor = None
    self.anagrams_table = None
    if not solutions_database is None:
      self.db = sqlite3.connect(solutions_database)
      self.dbcursor = self.db.cursor()
      self.dbcursor.execute("SELECT name FROM sqlite_master WHERE type='table' AND name='anagrams'")
      self.anagrams_table = self.dbcursor.fetchone()
      if self.anagrams_table is None:
        self.dbcursor.execute("CREATE TABLE anagrams (letters text primary key, solutions text)")

  def AddHand(self, hand):
    "Add entries for each word in the lexicon that can be formed by the given hand."
    assert _BUGPRINT("AddHand(%r)" % (hand,))
    if self.anagrams_table is None:
      self._AddLexiconForHand(hand)
      self._AddCombinationsForHand(hand)

  def _AddLexiconForHand(self, hand):
    '''For each word in the lexicon that can be formed by (hand) enter it
       into the correct hashtable, indexed by the sorted tuple of cards that
       can form it.'''
    # A typical 10-card hand will match 60 to 800 words, as many as 1700+, averaging about 140.
    # Use a quick regular expression matching test before trying to enumerate all possible matches.
    #   (speeds up this function from 5 sec to .75 sec for typical 10-card hand)
    assert _BUGPRINT("_AddLexiconForHand(%r)" % (hand,))
    assert all(c.isalpha() for c in hand)  # DO NOT CONSTRUCT REG-EX PATTERN FROM UNTRUSTED INPUT
    n = min(len(''.join(hand)), self.max_cards * self.max_chars_per_card)
    hand_re = re.compile("^[%s]{%d,%d}$" % ( ''.join(hand), self.min_cards, n ))
    counter = Incrementer()
    for word in self.lexicon:
      if hand_re.match(word):
          for (match,), remainder, unmatched in HandMatch(hand, word, permissive=False):
            if len(match) <= self.max_cards:
              key = tuple(sorted(match))
              self.combo_caches[len(key)][key].add(self.Word(match))
              assert counter.inc()
              assert _BUGEXEC('if counter._value % 100 == 0: print("added: %d\\r" % counter._value)', locals=locals())

  def _AddCombinationsForHand(self, hand):
    # Form all combinations of hands, up to the size of the given hand, or max_cards, whichever is smaller.
    #   2+2, 3+2, 3+3, 4+2, 4+3, 4+4, 5+2, 5+3, 5+4, 5+5, 6+2, 6+3,
    #   6+4, 6+5 (stop, too big), 7+2, 7+3, 7+4 (stop, too big),
    #   8+2, 8+3 (stop, too big)
    # Consider parallelizing this:
    #   Larger sums are dependent on the sums of their components.
    #   Equal sums just need to be merged (eliminating duplicates).
    #   A given sum (combination) can be arbitrarilly split up,
    #     processed independntly, and the results merged.
    assert _BUGPRINT("_AddCombinationsForHand(%r)" % (hand,))
    h = sorted(hand)
    n = min(len(hand), self.max_cards)
    for i in range(self.min_cards, n+1-self.min_cards): # 2..8 (if n=10)
      for j in range(self.min_cards, min(i,n-i)+1): # 2..2, 2..3, 2..4, 2..5, 2..4, 2..3, 2..2 (if n=10)
        target_dict = self.combo_caches[i+j]
        if i==j:
          iter_combo = NTH.iPairs(self.combo_caches[i])
          k = NTH.numSelections(len(self.combo_caches[i]), 2)
        else:
          iter_combo = itertools.product(self.combo_caches[i], self.combo_caches[j])
          k = len(self.combo_caches[i]) * len(self.combo_caches[j])
        assert _BUGPRINT("generating hand pairs %d+%d ( %5d x %5d -> %9d )" %
                  (i, j ,len(self.combo_caches[i]) ,len(self.combo_caches[j]) , k) )
        for kard_tuple in iter_combo:
          joint_cards = sorted(kard_tuple[0]+kard_tuple[1])
          assert _BUGPRINT( "trying combo %r -> %r %r ~= %r" %
                            (kard_tuple, joint_cards, type(joint_cards), h), debug=2 )
          #if NTH.isHeapSubset(heapq.merge(kard_tuple[0], kard_tuple[1]), h):
          if NTH.isHeapSubset(joint_cards, h):
            target_dict[tuple(joint_cards)].add(self.Pair(sorted(kard_tuple)))
          else:
            assert _BUGPRINT("  incompatible sub-hands: %r" % (kard_tuple,), debug=2 )
    assert _BUGPRINT("combo_cache sizes: "+', '.join(str(len(cc)) for cc in self.combo_caches))

  def Solutions(self, hand, length=None):
    "Yield all anagrams for the given hand."
    "Generate (points, words, unused_cards) solution tuples, ordered by len(unused_cards)."
    assert _BUGPRINT("Solutions(%r,%r)" % (hand,length))
    self.AddHand(hand)
    assert _BUGPRINT("Expanding solutions...")
    n = len(hand)
    sorted_hand = tuple(sorted(hand))
    hand_combo_hits = Incrementer()
    if length is None:
      # For each subset of cards in hand...
      itr = range(min(n,self.max_cards), self.min_cards-1, -1)  # Start with largest solutions first
    else:
      if length > self.max_cards:
        return # user probably forgot to specify larger max_cards
      itr = [length]  # Just look for solutions that use this many cards.
    for r in itr:
      # How to generate unique combinations of a multiset?
      # TODO: avoid generating repeated combinations by
      #  only generating combinations of set(hand) plus numbers of duplicates:
      #  for each combination of set(hand), # WRONG - what about "aaab" -> "aaa" with no "b"?
      #    for each combination of duplicate cards in hand,
      #      yield combined combination
      # TODO: avoid generating repeated combinations by
      #   only generating combinations/partitions of repeats of elements of set(hand)
      hand_combos_cache = set()
      for xs in itertools.combinations(range(n), r):  # r-length combinations of indexes into sorted_hand.
        subhand = tuple(sorted_hand[x] for x in xs)
        if subhand in hand_combos_cache:
          assert hand_combo_hits.inc()
          continue # don't bother to expand solutions for identical-looking subhands
        else:
          hand_combos_cache.add(subhand)
        unused = tuple(sorted_hand[y] for y in range(n) if not y in xs)
        value = TotalCardPoints(subhand) - TotalCardPoints(unused)
        for words in self._ExpandSolutionsFor(subhand):
          solution = (value, words, unused)
          yield solution
    # ** ERROR ** Should only yield unused hand if within length
    yield (-TotalCardPoints(hand), (), hand)
    assert _BUGPRINT("Solutions(%r) hand_combo_hits: %d" % (hand,hand_combo_hits.value()))

  def _ExpandSolutionsFor(self, hand, indent=0):
    '''Using previously constructed hashtables, yield tuples of sorted Words
       that the given (sub-)hand can be arranged into.'''
    hand = tuple(sorted(hand))
    assert _BUGPRINT("  "*indent+"IterSolutionsOf "+repr(hand), debug=2)
    assert isinstance(hand, tuple)
    cache = set()
    hits = Incrementer()
    #for solution in self.combo_caches[len(hand)].get(hand, set()):
    for solution in self._GetSolutions(hand):
      if isinstance(solution, self.Word):
        # Solution is a single word.
        if not (solution,) in cache:
          cache.add( (solution,) )
          yield (solution,)
        else:
          assert hits.inc()
          assert _BUGPRINT("DUPLICATE WORD! %r" % (solution,), debug=3)
      else:
        # Solution is a pair of disjoint sub-hands, each of which may have multiple
        #   solutions: Pair((M_CARD_SUBHANDS, N_CARD_SUBHANDS)) -> [ M1+N1, M1+N2, ... MI+NJ ]
        # Duplication is likley: an n-card hand that can be solved as 3 or more words
        #   will be stored the combo_caches only in pairs
        #   that get reconstituted into triples (or n-tuples) more than one way.
        assert isinstance(solution, self.Pair) and len(solution)==2
        for subsolution in itertools.product(*(self._ExpandSolutionsFor(h,indent+1) for h in solution)):
          assert _BUGPRINT("  "*indent+"subsolution: %r" % (subsolution,), debug=2)
          # Flatten the subsolution by 1 level.
          ss = []
          for item in subsolution:
            if isinstance(item, (self.Word,str)):
              ss.append(item)
            else:
              assert type(item) == tuple
              ss.extend(item)
          ss = tuple(sorted(ss))
          if not ss in cache:
            cache.add(ss)
            yield ss
          else:
            assert hits.inc()
            assert _BUGPRINT("DUPLICATE SUBSOLUTION: %r"%(ss,), debug=3)
    if hits.value():
      assert _BUGPRINT("_ExpandSolutionsFor(%r) cache hits: %d" % (hand, hits.value()))

  def _Dump(self):
    for i in range(2,len(self.combo_cache)):
      #ncombos = NTH.fact(self.ncards) / (NTH.fact(i) * NTH.fact(self.ncards-i))
      #ncombos = NTH.numCombinations(self.ncards, i)
      print("combo_cache[%d]: %d entries (of a possible %d)" % (i, len(self.combo_cache[i])))
      for key in self.combo_cache[i]:
        print(i,key,":",self.combo_cache[i][key])

  def ReportSolutions(self, hand):
    solutions = list(self.Solutions(hand))
    solutions.sort()
    for value, used, unused in solutions:
      if _DEBUG:
        print(value, used, " / ", unused)
        continue
      used_words = '  '.join('-'.join(w) for w in used)
      if unused:
        print("% 4d:  %s  -(%s)" % (value, used_words, '  '.join(unused)))
      else:
        print("% 4d:  %s" % (value, used_words))
    print(len(solutions),'solutions, %d bytes of RAM used' % self.GetSizeOf())

  def GetSizeOf(self):
    # Attempt to report how much memory is being used by this object.
    selfsize = sys.getsizeof(self)
    lexsize = sum(map(sys.getsizeof, self.lexicon)) + sys.getsizeof(self.lexicon)
    cdsize = DeepSizeOf(self.combo_caches)
    return selfsize+lexsize+cdsize

  # Replace multi-letter cards with just their first letter uppercased.
  squeezed   = dict( ( k, [k,k[0].upper()][len(k)>1] ) for k in Q_FREQS_ )
  unsqueezed = dict( ( [k,k[0].upper()][len(k)>1], k ) for k in Q_FREQS_ )
  #assert _BUGPRINT(repr(squeezed))
  def squeeze(self, cards):
    return ''.join(self.squeezed[c] for c in cards)
  def unsqueeze(self, s):
    return tuple( self.unsqueezed[q] for q in s )

  def Save(self):
    'Write solutions to disk.  Call any time after AddHand().'
    def solution2str(word_or_hands):
      if isinstance(word_or_hands, AnagramDictionary.Word):
        return self.squeeze(word_or_hands)
      else:
        return ','.join(self.squeeze(h) for h in word_or_hands)
    def packedSolutions(solution_set):
      "head;ad,eh"
      return ';'.join(solution2str(s) for s in solution_set)
    assert _BUGPRINT("inserting %d anagrams..." % sum(len(cc) for cc in self.combo_caches))
    # Note no attempt to avoid duplicates - this is a one-time insertion.
    self.dbcursor.executemany( "INSERT INTO anagrams(letters, solutions) VALUES (?,?)"
                             , ( (self.squeeze(k), packedSolutions(v)) for cc in self.combo_caches
                                                                       for k,v in cc.items() ) )
    self.close()

  def close(self):
    if hasattr(self, 'db'):
      assert _BUGPRINT("closing sql file")
      self.dbcursor.close()
      self.db.commit()
      self.db.close()

  def _GetSolutions(self, sorted_hand):
    assert sorted_hand == tuple(sorted(sorted_hand))
    solutions = self.combo_caches[len(sorted_hand)].get(sorted_hand)
    if not solutions is None:
      return solutions
    if self.anagrams_table is None:
      return set()
    self.dbcursor.execute("SELECT solutions FROM anagrams WHERE letters=?", (self.squeeze(sorted_hand),) )
    packed_solutions = self.dbcursor.fetchone()
    assert _BUGPRINT("packed_solutions = %r" % (packed_solutions,))
    if packed_solutions is None:
      return set()
    def str2solutions(s):
      t = s.split(',')
      if len(t) == 2:
        return self.Pair((self.unsqueeze(t[0]), self.unsqueeze(t[1])))
      assert len(t) == 1
      return self.Word(self.unsqueeze(t[0]))
    return list(map(str2solutions, packed_solutions[0].split(';')))

class TestAnagramSolver(unittest.TestCase):
  
  def setUp(self):
    self.lex = "bookkeeper cab cat he teeth the thee".split()

  def test_collections(self):
    self.assertTrue( collections.defaultdict(set)["ham"] == set() )
    self.assertFalse( "ham" in collections.defaultdict(set) )
    self.assertEqual( None, collections.defaultdict(set)["ham"].add(AnagramDictionary.Word(('h','a','m'))) )
    self.assertEqual( list(heapq.merge(('a','c','e','g'),('b','c','d','z')))
                    , sorted(          ('a','c','e','g')+('b','c','d','z')))

  def test_AnagramDict(self):
    solution1 = list(AnagramDictionary(self.lex).Solutions("a a b b c c".split()))
    self.assertTrue( ( 0, (('c','a','b'),             ), ('a','b','c')) in solution1 )
    self.assertTrue( (36, (('c','a','b'),('c','a','b')), ()           ) in solution1 )

    self.assertTrue( (45, (tuple("bookkeeper"),), ()) in
                     list(AnagramDictionary(self.lex).Solutions(list("bookkeeper"))) )

class Player(object):

  def __init__(self, name, lexicon):
    self.name = name
    self.lexicon = lexicon
    self.score = 0
    self.hand = Cards()
    self.seen = Cards()  # other cards seen outside of hand (for guessing what's in the deck)

  def Name(self): return self.name

  def Score(self): return self.score

  def NewGame(self):
    self.score = 0

  def AddScore(self, n):
    self.score += n

  def NewHand(self, hand, initial_discard_top):
    self.hand = hand

  def TakeTurn(self, game):
    "Given the current game state, decide what to do."
    # game interface:
    #   bool = game.MustGoDown()
    #   card = game.PeekDiscard()
    #   card = game.DrawDiscard()
    #   card = game.DrawDeck()
    #return (tuple_of_word_tuples, tuple_of_unused_cards)

class Computer(Player):

  def __init__(self, name, lexicon, anagramdict):
    Player.__init__(self, name, lexicon)
    #self.anagramdict = AnagramDictionary(lexicon)
    self.anagramdict = anagramdict

  def OtherPlayed(self, other, pickup, discard, laydown):
    pass

  def TakeTurn(self, game):
    "Given the current game state, decide what to do."
    # First: does picking up the discard enable laying down?  If so, do so.
    hypothesis = self.hand + [game.PeekDiscard()]
    best = (-1000, (), ())  # (points, words, unused)
    anadict = AnagramDictionary(self.lexicon)
    for (points, words, unused) in anadict.Solutions(tuple(hypothesis), length=len(self.hand)):
      # (81, (('q','u','a','r','k'), ('j','i','n','x')), ('i','o'))
      assert isinstance(unused, tuple)
      if len(unused) == 1 and points > best[0]:
        best = (points, words, unused)
    if best[0] > 0:
      c = game.DrawDiscard()
      assert isinstance(c, str)
      self.hand.append(c)
      d = best[2][0]
      assert isinstance(d, str)
      self.hand.remove(d)
      return (best[1], d)
    # Did not pick up discard.
    c = game.DrawDeck()
    assert isinstance(c, str)
    self.hand.append(c)
    anadict = AnagramDictionary(self.lexicon)
    best = (-1000, (), ())  # (points, words, unused)
    for r in range(len(self.hand)-1, 1, -1):
      for (points, words, unused) in anadict.Solutions(tuple(self.hand), length=r):
        assert isinstance(unused, tuple)
        if points > best[0]:
          best = (points, words, unused)
    assert _BUGPRINT("best = %r" % (best,))
    # Lay down whenever required or possible.
    if game.MustGoDown() or len(best[2])==1:
      discard = sorted(best[2], key=lambda c: Q_POINTS_[c])[-1]  # discard most expensive card
      laydown = best[1] + tuple(map(NTH.singleton, best[2][1:]))
      assert _BUGPRINT("laydown = %r, discard = %r" % (laydown, discard))
      assert isinstance(discard, str)
      assert isinstance(laydown, tuple)
      return (laydown, discard)
    # Not laying down, but still must discard.
    discard = self.hand.Pop()[0]  # arbitrary discard
    assert _BUGPRINT("discard = %r" % discard)
    assert isinstance(discard, str)
    return ((), discard)

#1234567890123456789012345678901234567890123456789012345678901234567890123456789
help_text = '''
  Type in your full or partial hand to rearrange your cards or connect them
into words.  You may do this as many times as you like.  Use hyphens to
separate letters without splitting words.  For example, if you had the
hand
  i  q  qu  t  u
and wanted to spell "quit" with the individual q and u cards, you could
type
  q-uit

  Before you go down, be sure that all but one of your cards is shown as
connected into words, if possible.  Any cards not connected into words when
you go down count against you.

Commands:
  /         Take the top discard.
  /?        Take a new card from the deck.
  .C        Discard card C and end your turn, going down only if required.
  !C        Discard card C and go down first, ending your turn.
  @exit     Exit the program.
'''

class Human(Player):

  def __init__(self, name, lexicon):
    Player.__init__(self, name, lexicon)
    self.help_counter = 0

  def NewHand(self, hand, initial_discard_top):
    Player.NewHand(self, hand, initial_discard_top)
    print('The discard pile starts with:  "%s"' % initial_discard_top)
    self.grouped_hand = tuple(map(NTH.singleton, self.hand))
    self.word_history = ()
    assert _BUGEXEC('self.PrintHand()', locals=locals())

  def PrintHand(self):
    MARGIN = ' '*4
    #print(MARGIN+' '.join(map(lambda c: '%2s'%c, self.hand)))
    #print(MARGIN+' '.join(map(lambda c: '%2d'%Q_POINTS_[c], self.hand)),"  (%d pts)" % TotalCardPoints(self.hand))
    assert _BUGPRINT(repr(self.grouped_hand))
    #print(MARGIN+'  '.join(map(lambda g: '-'.join(g), self.grouped_hand)))
    letters = [MARGIN]
    digits = [MARGIN]
    sum_points = 0
    max_points = 0
    i = 0
    while i < len(self.grouped_hand):
      j = 0
      pts = TotalCardPoints(self.grouped_hand[i])
      max_points += pts
      if len(self.grouped_hand[i]) > 1:
        sum_points += pts
      else:
        sum_points -= pts
      word_break = True
      while j < len(self.grouped_hand[i]):
        c = self.grouped_hand[i][j]
        if word_break:
          word_break = False
          fill = ' '
        else:
          fill = '-'
        letters.append((fill*3)[:3-len(c)]+c)
        digits.append(' %2d'%Q_POINTS_[c])
        j += 1
      i += 1
    sum_points = max(0,sum_points)
    print("\n%s   (%2d)\n%s   (%2d)\n" % (''.join(letters), sum_points, ''.join(digits), max_points))

  def OtherPlayed(self, other, pickup, discard, laydown):
    print()
    if pickup is None: pickup = "from the deck"
    else: pickup = ' "%s" ' % pickup
    print('%s picked up %s and discarded  "%s"' % (other.name,pickup,discard))
    if laydown:
      print("  and laid down: %s  (%d)" % ( '  '.join('-'.join(w) for w in laydown)
                                          , TotalWordPoints(laydown)))

  def RemoveCard(self, c):
    self.hand.remove(c)
    for i in reversed(range(len(self.grouped_hand))):
      for j in range(len(self.grouped_hand[i])):
        if c == self.grouped_hand[i][j]:
          self.grouped_hand = self.grouped_hand[:i] \
                            + (self.grouped_hand[i][:j],) \
                            + (self.grouped_hand[i][j+1:],) \
                            + self.grouped_hand[i+1:]
          self.grouped_hand = tuple([e for e in self.grouped_hand if e!=() and e!=''])
          return
    assert False

  def TakeTurn(self, game):
    print("\nYour turn.")
    drawn = False
    pickup = None
    while True:
      self.PrintHand()
      if not drawn: print('Top discard is:  "%s"  (%d pts)' % (game.PeekDiscard(), Q_POINTS_[game.PeekDiscard()]))
      if game.MustGoDown(): print('You will need to go down.')
      if self.help_counter == 0:
        print('Enter "?" for help.')
        self.help_counter = 6
      self.help_counter -= 1
      cmd = input("> ").strip()
      if cmd.startswith('?'):
        print(help_text)
      elif cmd == '/': # draw from discard pile
        if drawn:
          print("You already picked up on this turn.")
        else:
          pickup = c = game.DrawDiscard()
          print('You pick up the "%s" (%d)' % (c, Q_POINTS_[c]))
          self.hand.append(c)
          self.grouped_hand += ((c,),)
          drawn = True
      elif cmd == '/?':  # draw from deck
        if drawn:
          print("You already picked up on this turn.")
        else:
          c = game.DrawDeck()
          print('You drew:  "%s"  (%d)' % (c, Q_POINTS_[c]))
          self.hand.append(c)
          self.grouped_hand += ((c,),)
          drawn = True
      elif cmd.startswith('.') or cmd.startswith('!'):  # discard, and go down
        if not drawn:
          print("You must first draw.")
        else:
          c = cmd[1:].strip()
          if c in self.hand:
            laydown = ()
            self.RemoveCard(c)
            if cmd.startswith('!') and not game.MustGoDown() and any(len(w)<2 for w in self.grouped_hand):
              assert _BUGPRINT(repr(self.grouped_hand))
              self.hand.append(c)
              self.grouped_hand += ((c,),)
              print("You cannot go down first without using all of your cards.")
            elif cmd.startswith('!') or game.MustGoDown():
              for w in self.grouped_hand:
                if len(w) < 2 or ''.join(w) in self.lexicon:
                  laydown += (w,)
                else:
                  print("Not a legal word:  %s  (-%d)" % ('-'.join(w), TotalCardPoints(w)))
                  laydown += tuple(map(NTH.singleton, w))
            self.OtherPlayed(self, pickup, c, laydown)
            return (laydown, c)  # end turn (possibly going down)
          else:
            print("You don't have that card.")
      elif cmd.startswith('@'):  # escape command
        cmd = cmd[1:].strip().lower()
        if cmd in 'exit quit stop bye goodbye'.split():
          print("Bye!")
          sys.exit(0)
        elif cmd in 'shuffle'.split():
          random.shuffle(self.hand)
          self.grouped_hand = tuple(map(NTH.singleton, self.hand))
        elif cmd.split()[:1] in (['lookup'], ['search']): # look up regex in lexicon
          pattern = cmd[len('lookup')+1:]
          if pattern and len(pattern) <128:
            # TODO: secure against regular expression denial-of-service:
            #   re.search('a?'*25 + 'a'*25, 'a'*25)  # takes several seconds in Python!
            def ensafed(p):
              "Escape a string to make it a 'safe' regular expression."
              # For now, disallow (by escaping): + * ? {}
              s = []
              while p:
                if p[0] == '\\':
                  if len(p) > 1:
                    #if p[:2] == '\\v': s.append('[aeiou]')
                    #elif p[:2] == '\\c': s.append('[bcdfghjklmnpqrstvwxz]')
                    s.append(p[:2])
                elif p[0].isalnum() or p[0] in '.^$[]()|':
                  s.append(p[0])
                else:
                  s.append('\\'+p[0])
                p = p[1:]
              return ''.join(s)
            pattern = ensafed(pattern)
            rex = None
            try:
              rex = re.compile(pattern)
            except re.error as e:
              print(e)
            if not rex is None:
              matches = [k for k in self.lexicon.keys() if not rex.search(k) is None]
            #matches = [k for k in self.lexicon.iterkeys() if pattern in k]
            if len(matches) > 120 or not matches:
              print("%d words matching /%s/" % (len(matches), pattern))
              if pattern in self.lexicon:
                print("including:", pattern)
            else:
              matches.sort()
              print('\n'.join(matches))
        elif cmd in 'solve'.split():
          d = AnagramDictionary(self.lexicon)
          d.ReportSolutions(self.hand)
          self.AddScore( -int((len(self.hand)-1)*2.5) )  # 3 cards = -5 points, 11 cards = -25 points
        elif cmd in 'help'.split():
          print(help_text)
        elif cmd in 'ver version'.split():
          try:
            import time
            progname = os.path.join(os.getcwd(), sys.argv[0])
            progdate = time.localtime(os.path.getmtime(progname)) # or os.stat(progname).st_mtime
            print(sys.argv[0], "dated", time.strftime("%Y-%m-%d %H:%M:%S %Z", progdate))
          except:
            pass
          print("Python", sys.version.split()[0])
        else:
          print("Unknown command:", cmd)
      else: # rearrange hand
        #cmd = '%s %s' % (cmd, ' '.join('-'.join(w) for w in self.word_history))
        self.hand.reverse()  # find & remove from the right
        assert _BUGPRINT("calling HandMatch(%s, %s)" % (repr(self.hand), repr(cmd)))
        #for (words, spare, unmatched) in HandMatch(self.hand, cmd): print(words, spare, unmatched)
        words, spare, unmatched = next(HandMatch(self.hand, cmd))

        for wh in self.word_history:
          sp = list(spare)
          w = []
          for c in wh:
            if c in sp:
              w.append(c)
              sp.remove(c)
            else:
              break
          if len(w) == len(wh):
            words += (tuple(w),)
            spare = tuple(sp)
          if not spare:
            break

        spare = tuple(reversed(spare))
        assert _BUGPRINT("analysis: %r, %r, %r" % (words, spare, unmatched))

        new_groups = words + tuple(map(NTH.singleton, spare))
        new_hand = list(itertools.chain(*new_groups))

        if words:
          self.word_history = (words + self.word_history)[:64]
          assert _BUGPRINT("word_history = %r" % (self.word_history,))
        if unmatched != ():
          print("Not in your hand:", '  '.join(unmatched))

        assert _BUGPRINT("new_hand: %r %r" % (new_hand, type(new_hand)))
        #assert multiset.multiset(self.hand) == multiset.multiset(new_hand)
        assert collections.Counter(self.hand) == collections.Counter(new_hand)
        self.grouped_hand = new_groups
        self.hand = new_hand

        continue

        newhand = []
        self.hand.reverse()  # find & remove from the right
        i = 0
        while i < len(cmd):
          if cmd[i:i+2] in self.hand:
            newhand.append(cmd[i:i+2])
            self.hand.remove(cmd[i:i+2])
            i += 2
          elif cmd[i] in self.hand:
            newhand.append(cmd[i])
            self.hand.remove(cmd[i])
            i += 1
          elif cmd[i] == '-' or cmd[i] == ' ' or cmd[i] == '_':
            i += 1
          else:
            print("Not in your hand:", cmd[i])
            i += 1
        self.hand.reverse()
        self.hand = newhand + self.hand

class Game(object):

  def __init__(self, lexicon, nplayers=None):
    self.lexicon = lexicon
    # Make the computer players easier (and faster) by reducing their lexicons.
    # TODO: intersect frequencies with /usr/share/dict/words
    # TODO: eliminate more smaller words.  see: za
    #         I suspect the scrabble list is too flexible, while the nyt counts do not discriminate usage.
    ntokens = float(sum(lexicon.values()))
    assert _BUGPRINT("ntokens = %d" % ntokens)

    #self.smaller_lexicon = lexicon
    # scrabble-nyt-counts: (token count) / (total tokens):
    #   2E-7 = 42090 words
    #   9E-8 = .09/million = 51580 words
    #   4E-8 = 61649 words (similar to scrabble-words-common, intersection of scrabble-words and /usr/share/dict/words)
    #   3E-8 = 65270 words
    #   2E-8 = 70379 words
    #   1E-8 = 79015 words
    # Note that standard "uvalues" = 1E6 * count/total
    cutoff = 2E-7

    # Ideally, difficulty would be calibrated to word frequency, but what range of frequencies?
    # Simply using 1/10th to 10/10ths of the lexicon might be easier to compute.

    self.smaller_lexicon = dict( (k,v) for k,v in lexicon.items() if v/ntokens > cutoff)
    assert _BUGPRINT('len(smaller_lexicon) = %d' % len(self.smaller_lexicon))
    anagramdict = AnagramDictionary(self.smaller_lexicon)
    self.nplayers = nplayers
    if self.nplayers is None:
      self.AskNumPlayers()
    names = "Bender,Daneel,Data,Floyd,GLaDOS,Gort,Hal,Marvin,Shallow Blue,Robbie".split(',')
    random.shuffle(names)
    self.players = [Human("Human", lexicon)] + [Computer(names[i-2], self.smaller_lexicon, anagramdict) for i in range(2,self.nplayers+1)]
    self.first = random.randrange(self.nplayers)
    self.deck = None
    self.discard = None
    self.must_go_down = False

  def AskDifficultyLevel(self):
    while True:
      v = input("Choose difficulty level from 1 (easy) to 10 (hard) ?")
      if v.isdigit() and len(v) < 3:
        self.difficulty_level = int(v)
        if 1 <= self.difficulty_level <= 10:
          return
      print("You must specify a number from 1 to 10, where 1 is easiest and 10 is hardest.")

  def AskNumPlayers(self):
    while True:
      self.nplayers = input("Number of players (all but one will be played by the computer) ? ")
      if self.nplayers.isdigit():
        self.nplayers = int(self.nplayers)
        if 2 <= self.nplayers <= 8:
          return
      print("You must specify a number of players, from 2 to 8.")

  def NewGame(self):
    print("New game!")
    random.shuffle(self.players)
    print("The players are:", ', '.join(p.Name() for p in self.players))
    for p in self.players:
      p.NewGame()

  def Play(self):
    self.NewGame()
    for handsize in range(3,11):
      self.PlayRound(handsize)
      self.PrintScores()
      if handsize < 10:
        input("Press enter for next round...")
    print("\nGame over!")
    best_score = max(p.Score() for p in self.players)
    winners = [p for p in self.players if p.Score()==best_score]
    if len(winners) == 1:
      print("The winner is: %s with %d points!" % (winners[0].Name(), best_score))
    elif len(winners) > 1:
      print("%s and %s tied for %d points!" % ( ', '.join(w.Name() for w in winners[:-1])
                                              , winners[-1].Name()
                                              , best_score ))
    else: assert False
    print()
    return 0

  def PrintScores(self):
    print("\nTotal scores are:")
    for p in self.players:
      print("  %3d  %s" % (p.Score(), p.Name()))
    self.first = (self.first + 1) % self.nplayers

  def Deal(self, handsize):
    self.deck = Cards.FullDeck()
    self.deck.Shuffle()
    self.discard = Cards(self.deck.Pop()[0])
    for p in self.players:
      p.NewHand(self.deck.Pop(handsize), self.discard.Peek()[0])
    self.must_go_down = False

  def MustGoDown(self):
    return self.must_go_down

  def PeekDiscard(self):
    return self.discard.Peek()[0]

  def DrawDiscard(self):
    d = self.discard.Pop()[0]
    self.last_pickup = d
    return d

  def DrawDeck(self):
    self.last_pickup = None
    return self.deck.Pop()[0]

  def PlayRound(self, handsize):
    print("\nDealing %d cards each..." % handsize)
    self.Deal(handsize)
    print("%s goes first!" % self.players[self.first].Name())
    laydowns = [()]*self.nplayers
    i = self.first
    first_down = None
    while i != first_down:
      (laydowns[i], discarded) = self.players[i].TakeTurn(self)
      assert type(discarded)==str
      self.discard.Push([discarded])
      for j in range(self.nplayers):
        if j!=i:
          self.players[j].OtherPlayed(self.players[i], self.last_pickup, discarded, laydowns[i])
      if len(laydowns[i]) > 0 and first_down is None:
        first_down = i
        self.must_go_down = True
      i = (i + 1) % self.nplayers
    # In theory, players should have a chance to object to
    # other players' words at any point between laydown and end of round.
    print("\nRound over.")
    most_words   = (0,None)  # (count of most words, player with that count or None if more than one)
    longest_word = (0,None)  # (letters in longest word, player with that count or None if more than one)
    for i in range(self.nplayers):
      pts = 0
      wds = 0
      for w in laydowns[i]:
        ncards = len(w)
        if ncards > 1:
          pts += TotalCardPoints(w)
          wds += 1
          nletters = len(''.join(w))
          if nletters > longest_word[0]:
            longest_word = (nletters, i)
          elif nletters == longest_word[0]:
            longest_word = (nletters, None)
        else:
          pts -= TotalCardPoints(w)
      pts = max(0, pts)
      if wds > most_words[0]:
        most_words = (wds, i)
      elif wds == most_words[0]:
        most_words = (wds, None)
      print("%s played %d points." % (self.players[i].Name(), pts))
      self.players[i].AddScore(pts)
    if not most_words[1] is None:
      print("%s got the bonus for most words!  (%d words)" % (self.players[most_words[1]].Name(), most_words[0]))
      self.players[most_words[1]].AddScore(10)
    if not longest_word[1] is None:
      print("%s got the bonus for longest word!  (%d letters)" % (self.players[longest_word[1]].Name(), longest_word[0]))
      self.players[longest_word[1]].AddScore(10)
    if self.nplayers==2 and not most_words[1] is None and longest_word[1]==most_words[1]:
      print("  (Only one bonus counts in a 2 player game)")
      self.players[longest_word[1]].AddScore(-10)

def CmdDeal(args):
  assert _BUGPRINT("CmdDeal(%r)" % args)
  num_players = 1
  num_cards = random.randint(3,10)
  if args: num_cards = int(args.pop())
  if args: num_players = int(args.pop())
  if args:
    print("unknown arguments:", args)
    return 1
  deck = Cards.FullDeck()
  if num_players * num_cards > len(deck):
    print('sorry, no deal')
    return 1
  deck.Shuffle()
  for i in range(num_players):
    offset = i*num_players
    print(' '.join(deck[offset:offset+num_cards]))
  return 0

def CmdDeck():
  deck = Cards.FullDeck()
  random.shuffle(deck) # mutates global deck[]
  sys.stdout.write(' '.join(deck))  # avoid cr/lf; under CygWin `quid solve $(quid deck)` gets an extra \r !

def CmdPermute(cards):
  "Given a list of cards, find valid words."
  cards = sorted(cards)
  for p in itertools.permutations(cards):
    print(' '.join(p))

def CmdAddends(n):
  for a in NTH.Addends(int(n)): print(a)

def CmdSolveSlow(cards, lexicon):
  SolveSlow(lexicon, cards)

def CmdSolve_(cards, lexicon):
  v = AnagramSolver(lexicon, cards)
  v.ReportSolutions()
  return 0

def CmdSolve(cards, lexicon, database_filename):
  d = AnagramDictionary(lexicon, solutions_database=database_filename) # max_cards=10
  d.ReportSolutions(cards)
  return 0

def CmdSave(cards, lexicon, database_filename):
  d = AnagramDictionary(lexicon, solutions_database=database_filename) # max_cards=10
  d.AddHand(cards)
  d.Save()
  return 0

def CmdPlay(args, lexicon):
  numplayers = None
  handsize = None
  if args:
    numplayers = int(args.pop(0))
  if args:
    handsize = int(args.pop(0))
  print("\nA Word Anagram Game\n")
  print("** ALPHA VERSION **\n")
  try:
    import readline
  except ImportError:
    pass
  game = Game(lexicon=lexicon, nplayers=numplayers)
  try:
    if handsize is None:
      return game.Play()
    else:
      game.NewGame()
      game.PlayRound(handsize)
      game.PrintScores()
      return 0
  except (KeyboardInterrupt, EOFError):
    return 1

def CmdSpeedTest(args):
  import timeit
  def ti(stmt, setup='pass', number=1000):
    print("%-62s" % stmt, end=' ')
    print(timeit.timeit(stmt, 'import quid, heapq;'+setup, number=number))

  # Fastest way to test for small subsets of cards?
  ti("quid.HandMatch(['a','e','e','e','h','h','l','m','s','s','th','th','t','t','v'], 'themselthes', permissive=False)", number=10000)
  ti("quid.HandMatch0(['a','e','e','e','h','h','l','m','s','s','th','th','t','t','v'], 'themselthes')", number=10000)

  #multiset_setup = "hand = multiset.multiset('aeeehhlmssththttv')"
  #ti("multiset.multiset('themselthes').issubset(hand)", setup=multiset_setup, number=10000)
  #ti("multiset.multiset('bookkeepers').issubset(hand)", setup=multiset_setup, number=10000)

  ti("quid.NTH.isHeapSubset(sorted('themselthes'), 'aeeehhlmqqssttv')", number=10000)
  ti("quid.NTH.isHeapSubset(sorted('themselthen'), 'aeeehhlmqqssttv')", number=10000)
  ti("quid.NTH.isHeapSubset(sorted('bpefuelthen'), 'aeeehhlmqqssttv')", number=10000)

  print()

  # Fastest way to merge 2 small sorted tuples?
  merge_setup = "t1, t2 = ('a','c','e','g'),('b','c','d','z')"
  ti("list(heapq.merge(t1,t2))", setup=merge_setup, number=100000)
  ti("sorted(t1+t2)", setup=merge_setup, number=100000)

  print()

  ti("tuple(quid.NTH.iTriples(range(30)))")
  ti("tuple(quid.NTH.sTriples(range(30)))")

  ti("tuple(quid.NTH.iPairs(range(80)))")
  ti("tuple(quid.NTH.sPairs(range(80)))")
  ti("tuple(quid.NTH.iPairs_(range(80)))")

  ti("tuple(quid.NTH.iPowerSet(range(9)))")
  ti("tuple(quid.NTH.sPowerSet(range(9)))")

  ti("tuple(quid.NTH.iSubsetsK(range(18),3))")
  ti("tuple(quid.NTH.sSubsetsK(range(18),3))")

  return 0

def CmdUnitTest(args):
  unittest.main(argv=sys.argv[0:1]+args)

cmd_fns = \
  { 'deal'      : CmdDeal
  , 'deck'      : CmdDeck
  , 'permute'   : CmdPermute
  , 'anagram'   : CmdPermute
  , 'addends'   : CmdAddends
  , 'solveslow' : CmdSolveSlow
  , 'solve_'    : CmdSolve_
  , 'solve'     : CmdSolve
  , 'save'      : CmdSave
  , 'play'      : CmdPlay
  , 'report'    : Report
  , 'reportvowelconsonantstats' : ReportVowelConsonantStats
  , 'test'      : CmdUnitTest
  , 'unittest'  : CmdUnitTest
  , 'selftest'  : CmdUnitTest
  , 'speedtest' : CmdSpeedTest
  , 'shortlist' : ReportShortList
  }

def main(argv):
  global _DEBUG

  #defaultEncoding = locale.getpreferredencoding()
  mkopt = optparse.make_option
  #progname = os.path.splitext(os.path.basename(argv[0]))[0]
  parser = optparse.OptionParser(
    usage=__doc__,
    option_list = \
      [ mkopt('-d', '--debug', action='count')
      #, mkopt('--encoding',  action='store', default=defaultEncoding,
      #      help = 'specify ouput character encoding (current default = %s)' % defaultEncoding )
      , mkopt('-x','--lexicon', action='store', help='specify word list file to use', default='scrabble-word-counts.txt')
      , mkopt('--sqlite-file', action='store', help='specify sqlite3 database file to use', default=None)
      ]
  )
  opts, args = parser.parse_args(argv[1:])
  if opts.debug: _DEBUG = opts.debug
  if _DEBUG: print("_DEBUG = %r, opts = %r, args = %r" % (_DEBUG, opts, args))

  #sys.stdout = codecs.getwriter(opts.encoding)(sys.stdout)

  if args and args[0] in cmd_fns:
    f = cmd_fns[args.pop(0)]
    f_args = []
    arg_names = inspect.getargspec(f)[0]
    for aname in arg_names:
      if aname == 'opts':
        f_args.append(opts)
      elif aname == 'lexicon':
        opts.lexicon = os.path.join(os.path.dirname(sys.argv[0]), opts.lexicon)
        f_args.append(LoadLexiconF(opts.lexicon))
      elif aname == 'database_filename':
        f_args.append(opts.sqlite_file)
      elif aname == 'cards':
        if len(args) == 1:
          if '-' in args[0]:
            cards = args[0].split('-')
          else:
            cards = list(args[0])
        else:
          cards = args
        for c in cards:
          if not c in Q_POINTS_:
            print("invalid card:", c)
            return 1
        f_args.append(cards)
        args = []
      elif aname == 'args':
        f_args.append(args)
        args = []
      else:
        f_args.append(args.pop(0))
    f_args += args
    assert _BUGPRINT("f_args = %s" % repr(f_args)[:4096])
    return f(*f_args)
  elif args:
    print("unrecognized command:", ' '.join(args))
    return 1
  else:
    #suite = unittest.TestLoader().loadTestsFromTestCase(TestMatchers)
    #unittest.TextTestRunner(verbosity=2).run(suite)
    CmdUnitTest(args)

if __name__=='__main__':
  sys.exit(main(sys.argv))

