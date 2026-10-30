-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Part/MaskedSum4.lean: the masked sumcheck of a sub-proof, the verifier's part, as one
short text: the parameters of a call, the core (`complete`, `after`, `hidingAt`), the reading, then `hear`, `row`,
`whole`. A named part of the protocol: it has no place of its own; the kinds of block that sum something call it inside
their own texts. Definitions with code. No theorem.
The first message is read WHOLE (`firstRound`): every item of it is asked to be a scalar, THE
CALLER'S LEAD TOO. `leadScalars` is a
helper which no caller need use. `whole` takes the Call.

THE PROTOCOL. The prover claims that a polynomial S in the values of some committed maps, summed over some variables,
gives C, a linear form in values that it has sent only under masks. The sumcheck runs on H + eps S, H a hiding
polynomial whose coefficients are mask entries, and leaves ONE linear claim.
  ROUNDS   "PSC epsilon"  the caller's lead scalars, then mu, the sum of H      drawn: eps
           "PSC round"    once a variable: the round's polynomial g, lowest     drawn: r
                          coefficient first, WITHOUT THE ONE THAT THE ROUND'S
                          EQUATION FIXES: d - 1 scalars
           "PSC Y"        if there are ends: likewise, for one further          drawn: beta, never 0
                          variable, read at 0: dY scalars
           "PSC values"   the n end values, each as value + beta * its mask     drawn: nothing
  READS    nothing: no column is opened.
  DECIDES  `hear`: no equation is tested: what a sumcheck would test in a round is used to compute the coefficient
           that is not sent. `row`: the one claim that is left, a form that must be 0.
  SENDS    written in Lean in part alone: MaskedSumHonest.lean (lean/GAPS.md).

A hidden value. Every scalar that a sub-proof sends has a number, its slot. The hidden value under slot j is
shown_j - factor_j * mask_j. The ledger (`Model.Fork`) keeps for each slot what was shown, the factor, and whether it is
filled; and the next free slot.

WHAT IS CALLED BY NAME: the field's operations; forms on slots (`Model.Aff`) and the ledger's publicPart, hideRun, shown
(OnBytes/Model/Hide.lean), and its field next, which `hear` reads and writes: the ledger has a page of its own. ALL ELSE
STANDS HERE. The core is written after `verify-on-bytes`'s plain functions (OnBytes/Iop/Psc.lean: Weight.plain, equality,
complete, polyAt, claimAfter, hidingWalk; OnBytes/Model/Psc.lean: addSlots, Psc.rowForm), with a variable's two ways of
summing as two cases in the place of a record of four fields.

NOT HERE, AND WHERE IT IS. A round's name and kind, HOW MANY OF THE DRAWN ELEMENTS ARE NEVER 0, the numbers of positions and
matrix entries drawn, that no digest is drawn, the entry's rows, count, roots and answers, "nothing is owed": asked once for
all kinds where a block's rounds are held against the plan's entries, which a kind declares by `entries` OF THE SAME CALL.
That every word of a scalar is below the prime: the general fold's front. That beta is not 0: tested by nobody; the entry's
rule of drawing. The work bits of the rounds' entries: `entries` leaves them 0.
THE CALLER'S DUTY, which no line here can test: eps is drawn behind everything that C, the weights and S depend on. That
C is handed in at the beginning, and that every slot which it names is filled there (step 1), is what this text can do
for it. That an end value is the map's value at the point is a further claim of the caller's.
OF THE CALLER'S LEAD `hear` asks that it has k.lead items and that each is a scalar; it does not use their values. THAT THE
LEDGER F HAS TAKEN THEM, each under its slot, so that F.next is the slot of mu, is the caller's: no line here tests it.
Not claimed: that this text does what the text at OnBytes/K/Kc/Flat.lean:208-263 does, or its core what
`verify-on-bytes`'s does. Nothing on soundness, on an honest prover or on hiding.
-/
import OnBytes.Model.Hide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes
open OnBytes.Model (Aff Fork)

/-! ## The parameters of a call -/

/-- How a variable is summed. d: the number of coefficients of the round's polynomial g. -/
inductive Var where
  /-- g(0) + g(1) -/
  | plain (d : Nat)
  /-- (1 - z) g(0) + z g(1) -/
  | point (z : E) (d : Nat)

def Var.d : Var → Nat
  | .plain d => d
  | .point _ d => d

/-- The ends: the degree in the further variable Y, and the number of end values. -/
structure Ends where
  dY : Nat
  n : Nat

/-- A CALL. ROUNDS (`entries`), the tests on the plan (`shapeOk`) and the hearing (`hear`) all read this one record: a kind
that declares the rounds of a call and hears that call cannot declare one degree and hear another. -/
structure Call where
  /-- the caller's scalars in front of mu, in the first message -/
  lead : Nat
  /-- the variables -/
  vs : List Var
  ends : Option Ends

/-- The variables with Y, which is read at 0, behind them. -/
def Call.all (k : Call) : List Var :=
  match k.ends with
  | none => k.vs
  | some e => k.vs ++ [.point zeroE (e.dY + 1)]

/-- THE TESTS ON THE PLAN ALONE: they read no z. -/
def shapeOk (k : Call) : Bool :=
  (k.vs.all fun v => decide (2 ≤ v.d) && decide (v.d ≤ 65)) &&
    (match k.ends with
     | none => !k.vs.isEmpty
     | some e => decide (1 ≤ e.dY) && decide (1 ≤ e.n))

/-- An entry of the plan: so many scalars sent, so many elements drawn, so many of these never 0. -/
def entry (name : String) (sent drawn never0 : Nat) : Fmt.Entry :=
  { name := name, msg := 24 * sent, drawE := drawn, drawNZ := never0 }

/-- ROUNDS, as entries of the plan, the work bits left 0. -/
def entries (k : Call) : List Fmt.Entry :=
  [entry "PSC epsilon" (k.lead + 1) 1 0] ++ (k.vs.map fun v => entry "PSC round" (v.d - 1) 1 0) ++
    (match k.ends with
     | none => []
     | some e => [entry "PSC Y" e.dY 1 1, entry "PSC values" e.n 0 0])

/-! ## The core: the arithmetic of a sumcheck, on plain lists -/

/-- The polynomial with the coefficients g, lowest first, at x. -/
def valueAt (g : List E) (x : E) : E := g.foldr (fun c r => addE (mulE r x) c) zeroE

def total (l : List E) : E := l.foldl addE zeroE

/-- THE ROUND'S EQUATION, USED AS A DEFINITION: the round's polynomial, from what was sent and the running claim c.
Summed plainly, g(0) + g(1) = 2 g_0 + g_1 + g_2 + ..: the LINEAR coefficient is not sent. Summed at z,
(1 - z) g(0) + z g(1) = g_0 + z (g_1 + g_2 + ..): the CONSTANT one is not sent. -/
def complete : Var → List E → E → List E
  | .plain _, [], c => [c]
  | .plain _, g0 :: high, c => g0 :: subE c (addE (addE g0 g0) (total high)) :: high
  | .point z _, high, c => subE c (mulE z (total high)) :: high

/-- THE SUMCHECK AS A FOLD: the running claim behind the rounds: each round's polynomial at its challenge. -/
def after : List Var → List (List E × E) → E → E
  | v :: vs, (sent, r) :: rs, c => after vs rs (valueAt (complete v sent c) r)
  | _, _, c => c

/-- psi(r): psi is the variable's polynomial with the sum 1: X where the sum is plain, 1 where it is at a point. -/
def psiAt : Var → E → E
  | .plain _, r => r
  | .point _ _, _ => oneE

/-- a, a x, a x^2, ..: n members. -/
def powersFrom (x : E) : Nat → E → List E
  | 0, _ => []
  | n + 1, a => a :: powersFrom x n (mulE a x)

/-- THE HIDING POLYNOMIAL AT THE CHALLENGES, as a linear form in its coefficients, and P, the product of all psi(r).
H(X_1 .. X_k) = the sum over l of w_l(X_l) times the product of psi_j(X_j) over all j above l. The coefficients come by
variable, then by degree from 1 up; the LAST variable alone has a constant. -/
def hidingAt : List (Var × E) → List E × E
  | [] => ([], oneE)
  | [(v, r)] => (powersFrom r v.d oneE, psiAt v r)
  | (v, r) :: rest =>
    let later := hidingAt rest
    (powersFrom r (v.d - 1) (mulE later.2 r) ++ later.1, mulE later.2 (psiAt v r))

/-- How many coefficients H has: as many as the sumcheck's own scalars in front of the end values (the lead not counted). -/
def ownSlots (vs : List Var) : Nat := vs.foldl (fun n v => n + (v.d - 1)) 1

/-- f + u_0 (slot first) + u_1 (slot first + 1) + .. -/
def onSlots (f : Aff) (first : Nat) (u : List E) : Aff :=
  (u.foldl (fun (s : Nat × Aff) x => (s.1 + 1, Aff.addMul s.2 (Aff.slot s.1) x)) (first, f)).2

/-! ## Reading the rounds: no arithmetic -/

/-- What was read. -/
structure Read where
  /-- the sum of H -/
  mu : E
  eps : E
  /-- for each variable, Y last: what was sent, and the challenge -/
  rounds : List (List E × E)
  /-- the end values as shown -/
  values : List E

/-- A message's items as scalars; nothing if one is of another kind. -/
def scalars : List Fmt.ItemValue → Option (List E)
  | [] => some []
  | .e x :: l => (scalars l).map (E.ofTriple x :: ·)
  | _ :: _ => none

/-- A round in which n scalars are sent and k elements are drawn. -/
def roundOf (n k : Nat) (r : Fmt.RoundView) : Option (List E × List E) :=
  (scalars r.vals).bind fun s =>
    if s.length == n && r.drawn.elems.length == k then some (s, r.drawn.elems.map E.ofTriple) else none

/-- The variables' rounds: for each what was sent and the challenge; and the rounds behind them. -/
def varRounds : List Var → List Fmt.RoundView → Option (List (List E × E) × List Fmt.RoundView)
  | [], rs => some ([], rs)
  | _ :: _, [] => none
  | v :: vs, r :: rs =>
    match roundOf (v.d - 1) 1 r, varRounds vs rs with
    | some (s, [g]), some (l, rest) => some ((s, g) :: l, rest)
    | _, _ => none

/-- The first message, whole: the caller's lead; what stands behind it; what is drawn. EVERY ITEM IS ASKED TO BE A SCALAR. -/
def firstRound (k : Call) (r : Fmt.RoundView) : Option (List E × List E × List E) :=
  (roundOf (k.lead + 1) 1 r).map fun x => (x.1.take k.lead, x.1.drop k.lead, x.2)

/-- The caller's lead as scalars, for a caller that wants them so. `hear` does not call it, and no caller need. -/
def leadScalars (k : Call) (rs : List Fmt.RoundView) : Option (List E) :=
  rs.head?.bind fun r => (firstRound k r).map (·.1)

/-- What was read: mu, eps, the variables' rounds (Y's last), the end values. All rounds are used up. rs: the
sumcheck's own rounds, whole. -/
def readAll (k : Call) (rs : List Fmt.RoundView) : Option Read :=
  match rs with
  | [] => none
  | r :: rest =>
    match firstRound k r, varRounds k.all rest, k.ends with
    | some (_, [mu], [eps]), some (l, []), none => some ⟨mu, eps, l, []⟩
    | some (_, [mu], [eps]), some (l, [rv]), some e => (roundOf e.n 0 rv).map fun x => (⟨mu, eps, l, x.1⟩ : Read)
    | _, _, _ => none

/-! ## hear, row, whole -/

/-- What `hear` hands back. -/
structure Heard where
  /-- C, the form that the sum is claimed to equal -/
  start : Aff
  /-- T: C on what was shown -/
  target : E
  eps : E
  /-- the last running claim -/
  claim : E
  /-- the sumcheck's first slot -/
  first : Nat
  /-- the variables, Y last -/
  vars : List Var
  /-- the challenges, in the order of the rounds; beta last -/
  r : List E
  /-- the first end value's slot -/
  sEnd : Nat

/-- **The hearing.** C: the claimed sum. k: the call; that its variables' points are all known at the beginning is the
caller's duty, like C's: no line tests it. F: the ledger, BEHIND the caller's taking of its lead: the caller's duty too, and
no line tests it. rs: the rounds, whole. -/
def hear (C : Aff) (k : Call) (F : Fork) (rs : List Fmt.RoundView) : Option (Heard × Fork) := do
  guard (shapeOk k)
  let T ← F.publicPart C                                                           -- 1: every slot that C names is filled
  let h ← readAll k rs
  let all := k.all
  let c := after all h.rounds (addE h.mu (mulE h.eps T))                           -- 2; 3 and 4: the fold
  let r := h.rounds.map (·.2)
  let sEnd := F.next + ownSlots all
  let G ← ({ F with next := sEnd + h.values.length } : Fork).hideRun sEnd h.values.toArray (r.getLastD zeroE)  -- 5
  pure (({ start := C, target := T, eps := h.eps, claim := c, first := F.next, vars := all, r := r,
           sEnd := sEnd } : Heard), G)

/-- **The row**: the one claim that is left, a form that must be 0. h: AS hear GAVE IT (nothing here tests it). S0: the
summand at the point, on the SHOWN end values. kept: its terms in maps whose values are not shown. Both are the caller's,
as data. It takes no round. -/
def row (h : Heard) (S0 : E) (kept : Aff) (F : Fork) : Option (Aff × Fork) := do
  let (u, P) := hidingAt (h.vars.zip h.r)
  let G ← F.hideRun h.first (Array.replicate u.length zeroE) (subE zeroE oneE)      -- 7: H's coefficients: 0 shown, -1
  let f := Aff.ofConst (subE zeroE (subE h.claim (mulE h.eps S0)))                  -- 6: - (c - eps S0)
  let f := onSlots f h.first u                                                      --    + <u(r), H's coefficients>
  let f := Aff.addMul f (Aff.ofConst h.target - h.start) (mulE h.eps P)             --    + eps P (T - C)
  pure (Aff.addMul f kept h.eps, G)                                                 --    + eps kept

/-- What was shown under the end values' slots. -/
def shownEnds (h : Heard) (n : Nat) (F : Fork) : Option (List E) :=
  (List.range n).mapM fun j => F.shown (h.sEnd + j)

/-- **Both in a row**, for a caller WITH ENDS that makes its row at once; without ends: nothing. endTerm: S0 of the challenges
and the shown end values. -/
def whole (C : Aff) (k : Call) (endTerm : List E → List E → E) (F : Fork) (rs : List Fmt.RoundView) :
    Option (Heard × Aff × Fork) := do
  let e ← k.ends
  let (h, G) ← hear C k F rs
  let sh ← shownEnds h e.n G
  let (f, G') ← row h (endTerm h.r sh) {} G
  pure (h, f, G')

end VerifiableInference.Desc.Part.MaskedSum
