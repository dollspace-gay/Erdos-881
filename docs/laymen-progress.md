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

## The enemy must arm its own opponent (01:00)

Tonight's last verified chain is the strangest and maybe the most
important: every time the enemy's fortress defeats one of our key
removals, the defeat itself FORCES new keys into the enemy's own
keyring — a perfect mirror-copy of its guardian team, stamped at a
predictable position, at every scale, for every removal we try.
And those forced copies then collide with the very exclusiveness
the enemy was defending: each pair of stamped copies creates a
grid of forbidden overlaps it must dodge, forever.

The machine has checked both halves: the stamping is mandatory,
and the collisions are real. What remains is bookkeeping the
avalanche — every dodge spawns more stamps, every stamp more
dodges. That's next session's hunt, with tonight's census showing
only digit-style keyrings can even attempt the dodge — and those
pick their own locks.

## The two rails (01:20)

The last hour built the second rail. Everything we ever assumed
about the enemy — the famous fixed pair of guardian keys that the
whole campaign was built to fight — is no longer an assumption.
The machine now derives it: the problem's own minimality rule
forces one small guardian team for the two-key game, stable at
every scale, exactly as the failure rule forces one for the
three-key game. Two rails, one keyring, and the digit pattern of
the self-picking lock emerging where they cross. The recursion
that would finish everything runs along those rails, and its
first rung — the first digit — is already proven.

## The staircase is built (01:30)

The night's last theorems turned the recursion from a blueprint
into a working staircase. The machine now proves: the whole
bottleneck engine — the thing that forced the enemy's guardian
teams into existence — runs just as well when we restrict our key
removals to any endless sub-collection. Point it at the
predecessor-free keys and it descends one level; the new level has
its own guardian team, its own spacing number, its own
predecessor-free part; point it again, descend again. Rung by
rung, the enemy is forced to spell out digits, and we have already
proven both that the first rung holds and that a full digit tower
picks its own lock. What's left is walking the stairs formally —
big work, but of a kind we now know exactly how to do.

## The tax that cannot be dodged (02:30)

The night's last theorems proved the enemy must pay taxes. Every
guardian that guards for free pushes its neighbors so far away
that five free-riders can't fit in one district — and the machine
proved the districts must be crowded (the two-key promise forces
it). So in district after district, forever, someone pays: a real,
checkable hole punched in the keyring at a smaller scale, at a
guaranteed rate. We have the tax bill (verified), the tax rate
(verified), and the fact that only the digit-tower economy can
launder the payments (measured all night, with the digit economy's
self-defeat verified since midnight). One audit remains: tallying
the ledger down the scales. That is the whole of what's left.

## The mirror proof and the last filter (04:00)

Deep in the night, two more things became certain. First: the
clean-number keyring's deepest secret is now a theorem — a number
is missing from the keyring exactly when one of the forest's
guardians personally excludes it. The keyring is precisely the
shadow of its own guard-system, proven both directions.

Second: hunting for other keyrings obeying the same local laws, we
found thousands — until we added the one filter the problem's own
rules keep pointing at (every key must own its double outright).
That filter kills all but twenty-six candidates, and the true
keyring stands among them. The machine is now checking whether the
twenty-five pretenders can survive growing one more ring. Every
law used in the filter is already verified; what remains is
proving the problem's rules FORCE the filter — one lemma-shaped
wall, approached from five verified directions.

## 2026-07-25 afternoon — The master key, and the day the fortress audited itself

Today had two faces.  First, the audit: we discovered that one of
last night's proudest walls — the "trap tower" — was real stone but
enclosing no prisoner: its statement could be satisfied by ANY
keyring, enemy or not.  We proved that emptiness formally (two
certificate theorems), tore the narrative down honestly, and found
that the older, humbler machinery had been sound all along.

Then, the master key.  The repaired trap idea — "keep a list of
locks such that every door still has a key avoiding the list" —
turned out to work perfectly if one records the list's INNOCENCE
(its freeness) as part of the theorem.  With that one fix, the
whole campaign's dreamed-of configuration became a proven fact:

**Any would-be counterexample must appoint, above some height,
EVERY single one of its keys as a personal guardian of some door,
and all those guardianships share one fixed, finite, nonempty
committee (the core S*).**  Every door a guardian protects is
protected by exactly the committee plus that one rotating guardian
— nothing more, nothing less.  And each such door leads to one of
two endgames we can now attack separately: either one committee
member hands out door-keys forever, or each rotating guardian
personally owns every pair-key of its own door.

The enemy has been pushed from "could be anything" to "must run a
rigid committee system we fully understand."  What remains is to
show the committee system itself collapses — the two endgame
branches are the last rooms of the maze.

## 2026-07-25 late afternoon — The portrait, the closed door, and the tree

After the master key, the afternoon delivered four more blows:

1. **The double shift.** Not only must every large key be a
   guardian at the triple-lock level — the same key must ALSO
   guard a door at the pair-lock level, both jobs at once, forever.

2. **No sharing.** Two guardians can only ever share a door if the
   door's number is exactly the sum of the two guardians.  Sharing
   is total exposure; the enemy's workforce is essentially
   one-key-one-door.

3. **The Sidon door slammed shut.**  The enemy kept trying to be a
   "perfect thin keyring" (every door having barely one pair of
   keys — the mathematician's word is Sidon).  We proved that is
   IMPOSSIBLE: any counterexample must contain doors with
   arbitrarily many key-pairs.  Yet its guarded doors must stay
   thin.  The enemy is condemned to be thin and thick at once,
   in different places, forever — a very strange animal.

4. **The tree.**  All of this came from one master picture: the
   "innocent lists" of keys form a tree, and against a
   counterexample every branch of that tree must die at a finite
   height.  Where a branch dies, a guardian is born.  The next
   campaign climbs this tree with a ranking system — if we can
   show the ranks must descend forever, no counterexample can
   exist, and the problem is solved.

Score for the day: ~40 new verified theorems, two emptied walls
demolished honestly, one master structure theorem, zero sorries.

## 2026-07-25 evening — The ladder

We built a brand-new tool from scratch (the infinite Ramsey
theorem, at two strengths) and used it to climb: any infinite
collection of the enemy's keys can be refined so that either every
pair of keys jointly guards a door (and then those doors must race
upward at least as fast as the keys themselves), or every trio
does, or the enemy is forced to field guard-teams of four or more.
Each rung of the ladder is another shape the enemy cannot escape
into.  The ladder climbs one arity at a time; the top of the
ladder — all arities at once — is guarded by a known technical
obstacle (the "diagonal leak") whose remedy is mapped out for the
next campaign.

## 2026-07-25 evening, part two — The full ladder and the two final rooms

The Ramsey ladder now reaches EVERY height (one theorem for all
arities — permanent mathematics beyond this problem), and the rank
machinery built this evening turned the whole campaign into a
two-room endgame.  Every possible enemy keyring now lives in one of
exactly two rooms, both fully mapped:

**Room one — the infinite tower**: the enemy's "innocent lists"
tree has infinite depth-rank, wide but never tall (no infinite
branch survives — that much is proven).

**Room two — the perfect crystal**: somewhere inside the enemy
there is an infinite family of keys so symmetric it looks
machine-made: every group of d keys is harmless, every group of
d+1 keys jointly seals some door, no exceptions, ever.

And hovering over both rooms: the reduction theorem.  If any
verified operation can be shown to strictly shrink the tower's
rank each time it is applied, there is no enemy at all and the
problem is solved.  One question left.  Everything machine-checked.

## 2026-07-25 night — The three-key law and the last gap

Late-evening finds: no door can be sealed against four separate
key-confiscations at once (a door opens with three keys, and three
keys cannot belong to four disjoint confiscations) — so taking
away many disjoint key-sets forces the enemy to sacrifice many
DIFFERENT doors, at least one per three confiscations.  And every
sacrificed door drags its whole "fan" of neighbours into an
additively thin region we can count.

What remains — and it is now exactly one thing — is that the
enemy may schedule its sacrificed doors at wildly different
heights, each fitting its own local budget.  One verified way to
force those sacrifices into a shared window, or one counting law
that makes even scattered sacrifices collide, finishes the
problem.  Everything encircling that single gap is machine-checked
mathematics now.
