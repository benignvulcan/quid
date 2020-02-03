# quid.py

A word anagram game, similar to the game described at https://en.wikipedia.org/wiki/Quiddler

This program runs in a terminal.  It supports only 1 non-AI player.

Here is the beginning of an example run:

```

A Word Anagram Game

** ALPHA VERSION **

Number of players (all but one will be played by the computer) ? 3
New game!
The players are: Gort, Daneel, Human

Dealing 3 cards each...
The discard pile starts with:  "b"
Gort goes first!

Gort picked up from the deck and discarded  "h"
  and laid down: h-o-g  (15)

Daneel picked up from the deck and discarded  "o"
  and laid down: l-i-e  (7)

Your turn.

      d  z  a   ( 0)
      5 14  2   (21)

Top discard is:  "o"  (2 pts)
You will need to go down.
Enter "?" for help.
> adz

      a--d--z   (21)
      2  5 14   (21)

Top discard is:  "o"  (2 pts)
You will need to go down.
> /?
You drew:  "t"  (3)

      a--d--z  t   (18)
      2  5 14  3   (24)

You will need to go down.
> !t

Human picked up from the deck and discarded  "t"
  and laid down: a-d-z  (21)

Round over.
Gort played 15 points.
Daneel played 7 points.
Human played 21 points.

Total scores are:
   15  Gort
    7  Daneel
   21  Human
Press enter for next round...
```

## License

GNU GPL v3+

## Requirements

* Python 3

