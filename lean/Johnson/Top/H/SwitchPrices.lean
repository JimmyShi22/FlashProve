-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/SwitchPrices.lean: the conditions under which the plan's two errors cover the two
errors of the code switch (`SendLocPrices`, OnBytes/Tie/Pv/Switch/SendLocPrices.lean), at the caller
`switchOf` (Johnson/Top/H/SwitchBehindFold.lean): the one on the numbers of seeds holds outright;
the one on clashing seeds holds where the setting's field, its answers a sample and the samples'
cubes are the library's; the others are left as conditions on the planner's numbers.

`SendLocPrices z s o g idx` has eight fields. At `switchOf` the family is `sigOf cs l` under the
joint seeds `seedsOf cs l`. `marginals` is then arithmetic on the numbers of seeds
(Johnson/Pack/PortErr.lean: `card_D`, `mult_eq`). `clash` holds with equality at one answer a
sample: a member's number of clashing seeds (`zerr_def`) is the planner's `clashSeeds`, and its
number of seeds is the planner's `allSeeds` (OnBytes/Params/RecordPrice.lean), at the field's size
and the member's cube. Johnson/Top/H/SendAt.lean has the like for the kind of a sending alone, in
one law (`term_share`, `sendAt_covered`); here the two factors stand apart, in the form that the
fields of `SendLocPrices` ask. Statements and proofs.
Main names:
  `card_ZD`: a member's seeds are q ^ b (q - 1), q the size of the field, b its cube's bits.
  `marginals_of`, `clash_of`: the two fields, of `sigOf cs l` and `seedsOf cs l`.
  `switchOf_prices`: `SendLocPrices (switchOf ..) s o g idx`, if the setting's field has the size of
    the library's, it has one answer a sample, the cube at a member's place in o has the member's
    bits, `lOf` at each member is at most the planner's list size there, the group g is priced
    under the Johnson rule with a count that is not marked bad, and the group's joint radius passes
    `upperRadiusTest`.
Limits: the conditions that are left are shown at no numbers here; Johnson/G/SwitchPricesLit.lean
has written numbers. idx is any enumeration. Nothing on proof of work.

-/
import Johnson.Top.H.SwitchBehindFold
import Johnson.Pack.PortErr
import OnBytes.Tie.Pv.Switch.SendLocPrices

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes.Slice Cb Iop IOR Johnson.Pack OnBytes OnBytes.Params OnBytes.Plan
open OnBytes.Tie.Pv.Switch

/-- A member's seeds. -/
theorem card_ZD (cs : OnBytes.Codes) (sh : OnBytes.OracleShape) :
    Fintype.card (portZ cs sh).D =
      Fintype.card GE ^ bitsZ cs sh * (Fintype.card GE - 1) := by
  show Fintype.card ((Fin (bitsZ cs sh) → GE) × GEˣ) = _
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, cardU GE]

section
variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))

/-- Exact marginals. -/
theorem marginals_of (i : Fin l.length) :
    (seedsOf cs l).mult i * Fintype.card (portZ cs (l.get i).1).D =
      Fintype.card (seedsOf cs l).D := by
  rw [mult_eq, card_ZD, card_D, ← Nat.mul_assoc, ← pow_add,
    Nat.sub_add_cancel (bits_le cs l i)]

/-- A member's clashing seeds against the planner's share, at one answer a sample. -/
theorem clash_of (i : Fin l.length) :
    (portZ cs (l.get i).1).err * allSeeds (Fintype.card GE) (bitsZ cs (l.get i).1) ^ 1 ≤
      clashSeeds (Fintype.card GE) (bitsZ cs (l.get i).1) ^ 1 *
        Fintype.card (portZ cs (l.get i).1).D := by
  rw [zerr_def, card_ZD, pow_one, pow_one]
  exact le_rfl

end

variable {S : Sig GE} {G : Grp S} [Nonempty G.P] {Sh : GShape G} {kp : S.O → Prop}
  [DecidablePred kp] (Hd : GHeld Sh kp) {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) G.C.J) (Z : Evader GE (G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (cutN : (sigOf cs l).Msg → (Hd.foldD Sb sl Z A₀).Cf.N.Wit) (t : ℕ)
  (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W) {Pw : Type} (Cw : LdCode GE Pw)

/-- The conditions on the prices at the caller, from conditions on the planner's numbers. -/
theorem switchOf_prices (s : Setting) (o : List SampleSize) (g : GroupSize)
    (idx : Fin l.length ≃ Fin o.length) (hq : s.cardE = Fintype.card GE) (hs : s.samples = 1)
    (hcube : ∀ i, (o.get (idx i)).cubeBits = bitsZ cs (l.get i).1)
    (hlist : ∀ i, lOf cs (l.get i).1 (l.get i).2 ≤ largestList s (o.get (idx i)).groups)
    (rule : g.rule = .johnson) (source : (analysisOfM s g).mainAt.source = .johnson)
    (counted : (analysisOfM s g).mainAt.count.bad = false)
    (radius : upperRadiusTest s g G.e = true) :
    SendLocPrices (switchOf Hd Sb sl Z A₀ cs l cutN t w₀ Cw) s o g idx where
  field := by
    rw [hq]
    exact two_le_card
  marginals := fun i => marginals_of cs l i
  clash := fun i => by
    show (portZ cs (l.get i).1).err * allSeeds s.cardE (o.get (idx i)).cubeBits ^ s.samples ≤
      clashSeeds s.cardE (o.get (idx i)).cubeBits ^ s.samples *
        Fintype.card (portZ cs (l.get i).1).D
    rw [hq, hs, hcube i]
    exact clash_of cs l i
  lists := hlist
  rule := rule
  source := source
  counted := counted
  radius := radius

end Johnson.Top.H

#print axioms Johnson.Top.H.marginals_of
#print axioms Johnson.Top.H.clash_of
#print axioms Johnson.Top.H.switchOf_prices
