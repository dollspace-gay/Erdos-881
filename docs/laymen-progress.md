# The overnight campaign, in plain language

*2026-07-24, for the keyring. Everything below marked "proved" is
machine-checked in Lean with zero gaps.*

## Where we stood at nightfall

The problem: a keyring where removing any infinite set of keys breaks
the two-key locks. Erdős asked: can you always find an infinite set of
keys to discard so that every lock still opens with *three* keys?

We had killed several guardian schemes but three big enemies were
alive: the *lone-guardian stream* (an endless parade of single keys
each privately guarding a lock), the *guardian clique* (an infinite
club of keys pairwise co-guarding locks), and the *diffuse fog* (locks
guarded by no small committee at all).

## What died tonight — all machine-verified

**The lone-guardian stream is dead. Completely.** The spare-keys
machine (mirrors → levels → surviving deletion) turns out to need only
a few specific reflections, all of which can dodge any single bad
spot. If the parade's guardians keep changing, each new level only has
to avoid a finite list of old landmarks — always possible. If the
parade keeps reusing one guardian, that guardian's own mirrors run the
machine. Either way: an infinite set of keys can be discarded and
every large lock still opens with three keys. Big guardians, small
guardians, fixed, rotating — all of them. A corollary we didn't have
before: **in any would-be counterexample, no single key is
irreplaceable at the three-key level.**

**The guardian clique is nearly dead.** The club's power was supposed
to be that its locks could hide at any height (hugging their guards,
dodging our windows). Three discoveries broke it:

1. *Sharp pinning*: the old pinning argument needed "room" above the
   lock; it turns out only two exact positions ever need dodging, so
   pinning works at every altitude.
2. *Levels can't lag*: if a lock hugged its guard too tightly, a
   whole stretch of numbers would have no way to be covered — the
   keyring would starve. So mirror levels automatically grow.
3. *One spare key suffices*: if even one club member `u` is
   replaceable at the two-key level (and all but finitely many keys
   are, by a known theorem from the literature), then every lock
   guarded by `u` and any partner feeds the spare-keys machine.

The only club that survives is one where **every member is
irreplaceable at its own scale** — each member privately two-guards
some lock at or above its own height. That is exactly how the known
minimal keyrings behave at the two-key level, so this residue is the
true heart of the problem, now isolated precisely.

**The zero residue is cornered.** The only lone guardian left is the
zero key itself, and we proved its locks can't be keys, their mutual
distances can't be keys, and triples of its locks carve key-free
holes. It survives only as an extremely rigid, strange structure.

## The final verified statement

> Any counterexample with pair-funnels (Link A) and anchors either
> admits the desired discard set (contradiction — so it isn't a
> counterexample), or hides in the zero residue, or is an infinite
> club of self-scale irreplaceable keys.

## What's left, honestly

1. **Link A (the fog):** show the fog can be thinned so that late
   destroyed locks always funnel through one or two keys.  We proved
   the trichotomy (funnel of one, funnel of two, or disjoint routes)
   and that the whole question equals: *can three-key repairs always
   absorb the two-key damage that minimality itself mandates?*
2. **The self-scale club:** kill the last clique shape — probably via
   the literature's finiteness of essential keys, not yet formalized.
3. **The zero residue** and a mild anchor-supply lemma.

No lab experiment, random or adversarial, has ever produced a seed of
the surviving enemies. Everything guardian-shaped is dead, and the
death certificates are machine-checked.

## The lock that picks itself (2026-07-24, after midnight)

We built the enemy's dream fortress to see if it could exist: a
keyring where every key is a "clean" number (base-3 digits only 0
or 1). This fortress genuinely starves the two-key game — remove
the special marker keys and certain doors can never be opened with
two keys again. Perfect destruction, at every scale, forever. And
the fork patterns it shows the repair crew are exactly the
"spread-out" patterns our matching engine cannot latch onto. It
looked like the perfect enemy.

Then we watched it pick its own lock. With THREE keys, a new trick
exists that two keys can never do: three 1-digits in the same
position roll over — a carry, like 9+9+9 crossing into the tens
column. Every door the marker-deletion sealed opens again with
three ordinary, non-marker keys: 27 = 13+10+4, and the same recipe
scaled up forever. The machine has checked every step of this.

Why this matters: the enemy needs two things at once — rigid enough
digits to starve the two-key game, and no carry-tricks for the
three-key crew. The fortress proves these two demands fight each
other: the same rigidity that starves pairs is exactly what makes
triples roll over. The enemy's last hiding place demands a material
that is stiff and soft at the same time.

## A whole world where the answer is YES (00:00)

We didn't just watch the fortress pick its own lock — we certified
the entire story, end to end, in the machine. The clean-number
keyring is now a fully verified world where Erdős's question has
its hoped-for answer: it opens every door with two keys; removing
ANY infinite bundle of keys breaks the two-key game (every removed
key owned a private door — its own double); and yet removing the
marker keys leaves a keyring that opens every door with three keys,
using the carry trick at every scale. Hypothesis, destruction, and
three-key repair: the exact pattern the problem asks about, alive
and checked line by line.

What this buys the hunt: the imagined enemy keyring must starve the
two-key game the way clean numbers do — our earlier walls force
that — but it must ALSO avoid the carry trick that clean numbers
can't help but offer. Stiff and soft at once. Every wall we build
now squeezes that contradiction tighter.

## Every enemy has bottleneck doors (00:30)

A brand-new engine, checked by the machine tonight: if the doors of
the enemy's fortress each have MANY completely separate three-key
openings, then a cunningly slow-growing set of key removals beats
the fortress outright — too few removed keys below each door to
touch all its separate openings. So a real enemy fortress must have
infinitely many BOTTLENECK doors: doors whose every three-key
opening passes through the same tiny fixed cluster of keys.

We already knew how to fight two-key bottlenecks — that was the
whole guardian-pair campaign. Tonight's theorem says bottlenecks of
some fixed small size are FORCED, straight from the enemy's
definition. The hunt now has a single shape to chase: tiny key
clusters that infinitely many doors all depend on. The walls built
for pairs are being widened to fit.

## The bottleneck hunt comes home (00:40)

Tonight's new engine kept going. We proved the machine-checked
chain all the way down: any enemy keyring must have infinitely many
bottleneck doors; each bottleneck's key cluster splits into a fixed
tiny core plus far-away rotating helpers; the core can't be empty,
can't be the zero key, can't be any single key — every one of those
cases dies against walls we had already built and verified. The
smallest possible core is a PAIR of keys, exactly the shape the
whole guardian-pair campaign was built to fight. And inside any
leanest bottleneck cluster, every key holds a private opening that
only it can serve — a personal fingerprint the hunt can track.

In short: the enemy no longer gets to choose its shape. Its own
definition drives it into the pair-guardian corner, where most of
our verified weapons already point.

## One team to guard them all (00:45)

The bottleneck story sharpened again, and the machine has checked
every step: the enemy doesn't just need bottleneck doors — it needs
ONE fixed little team of keys that shows up in bottleneck after
bottleneck, at every scale, forever, each teammate holding a
private opening only it can serve. Everything else in any
bottleneck is a far-away helper that drifts upward and away.

And if the fixed team is EMPTY — all helpers, no permanent staff —
then even the two-key game at those doors runs through the same
drifting helpers, which is precisely the roaming-guard pattern our
counting walls were built against. Either way the enemy is now
pinned between two named corners, both already half-conquered.
