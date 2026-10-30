-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/G/SwitchAtSmall.lean: the condition of the caller `switchOf` of the code switch, at the
written sendings of the small example (Johnson/G/PackLit.lean): it is left with one premise, the
laws of the choice of kept messages.

The small example's twin of Johnson/G/LinkLit.lean, Johnson/G/BatAtFull.lean (as far as the members'
test goes) and Johnson/G/SwitchAtFull.lean. Definitions, statements and proofs; the tests on numbers
are theorems by an evaluation in Lean's kernel.
Main names:
  `frameSmallLit`: the first 16 elements of `packSmallLit` under the proof's codes `codesSmall2`.
  `linksSmallLit`: 6 lists: these joined three by three (`byThree`), and the last one alone.
  `linksSmallLit_meets`: `Johnson.Pack.allMeet` at the proof's codes is true at each of the 6.
  `logSmall`, `radSmall`, `distSmall`: 18; 76,267; 130,855: the logarithm of a common length, a
    joint radius, a distance. `links_fit_small`: every message of each of the 6 lists meets
    `MemberFits` at these numbers. `links_john_small`: the radius is below the Johnson radius.
  `fits_small`: `Grp.Fits` of `grpOf codesSmall2 l mem logSmall radSmall`, at each of the 6 lists,
    for every choice of members. `posSmall`: that group has a position.
  `switch_ok_small`: at each of the 6 lists, every choice of members, every shape of that group,
    every choice Hd of kept messages that has its laws, and every element x of `packSmallLit`:
    `SendLocRide.OK` of `switchOf Hd .. x.1 x.2 ..`.
Limits: those of Johnson/G/PackLit.lean. That the first 16 sendings under the proof's codes are the
first chain's, three a link and one for the last group, is read off the lists' lengths and is held
by no test here. That 18, 76,267 and 130,855 are the planner's numbers is not shown: the radius is
that of the lists' own messages of the common length; the distance is the least of the members' as
read at the common length. Which list is the group in front of which sending is not said: the
statement holds at every pair. No shape and no choice of kept messages is written here, and
`GHeld.Laws` is shown of none. That a switch of the programs' protocol is a value of `switchOf` is
not said. The condition says nothing on the size of the errors.

-/
import Johnson.Top.H.SwitchBehindFold
import Johnson.G.LinkLit
import Johnson.Pack.BatSize

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G
open OnBytes OnBytes.Slice Johnson.Pack Johnson.Top.H Cb Iop IOR

/-- The first 16 sendings under the proof's codes: each one's sampled messages. -/
def frameSmallLit : List (List (OracleShape × Nat)) :=
  ((packSmallLit.dropWhile fun x => decide (x.1 ≠ codesSmall2)).take 16).map (·.2)

/-- These joined three by three; the last one alone. -/
def linksSmallLit : List (List (OracleShape × Nat)) := byThree frameSmallLit

theorem linksSmallLit_length : linksSmallLit.length = 6 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The test holds at each whole list. -/
theorem linksSmallLit_meets :
    (linksSmallLit.all fun l => Johnson.Pack.allMeet codesSmall2 l) = true := by
  decide +kernel

/-- the logarithm of the common length -/
def logSmall : ℕ := 18
/-- the joint radius -/
def radSmall : ℕ := 76267
/-- the distance -/
def distSmall : ℕ := 130855

theorem links_fit_small : ∀ l ∈ linksSmallLit, ∀ x ∈ l,
    MemberFits codesSmall2 logSmall radSmall distSmall x.1 x.2 := by decide +kernel

theorem links_john_small : InJohnson (2 ^ logSmall) distSmall radSmall := by decide +kernel

/-- The joint radius implies each member's own, at each of the 6 lists. -/
theorem fits_small (l : List (OracleShape × ℕ)) (hl : l ∈ linksSmallLit)
    (mem : Fin l.length → Prop) [DecidablePred mem] :
    (grpOf codesSmall2 l mem logSmall radSmall).Fits :=
  grp_fits codesSmall2 l mem logSmall radSmall
    (fun i _ => (links_fit_small l hl (l.get i) (List.get_mem l i)).le)
    fun i _ => (links_fit_small l hl (l.get i) (List.get_mem l i)).near

/-- The group has a position. -/
instance posSmall (l : List (OracleShape × ℕ)) (mem : Fin l.length → Prop)
    [DecidablePred mem] : Nonempty (grpOf codesSmall2 l mem logSmall radSmall).P :=
  ⟨⟨0, Nat.two_pow_pos _⟩⟩

/-- The kind's condition, left with the kept messages' laws. -/
theorem switch_ok_small (l : List (OracleShape × ℕ)) (hl : l ∈ linksSmallLit)
    (mem : Fin l.length → Prop) [DecidablePred mem]
    {Sh : GShape (grpOf codesSmall2 l mem logSmall radSmall)}
    {kp : (sigOf codesSmall2 l).O → Prop} [DecidablePred kp] (Hd : GHeld Sh kp) (hL : Hd.Laws)
    {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
    (sl : ∀ b, Slf GE (Sb b) (grpOf codesSmall2 l mem logSmall radSmall).C.J)
    (Z : Evader GE ((grpOf codesSmall2 l mem logSmall radSmall).Row B)) {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀ (((sigOf codesSmall2 l).sub kp).Msg × Wp))
    {x : Codes × List (OracleShape × ℕ)} (hx : x ∈ packSmallLit)
    (cutN : (sigOf x.1 x.2).Msg → (Hd.foldD Sb sl Z A₀).Cf.N.Wit) (t : ℕ)
    (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W) {Pw : Type} (Cw : LdCode GE Pw) :
    Cb.Pv.SendLocRide.OK (switchOf Hd Sb sl Z A₀ x.1 x.2 cutN t w₀ Cw) :=
  switchOf_ok Hd Sb sl Z A₀ x.1 x.2 cutN t w₀ Cw
    (List.all_eq_true.1 packSmallLit_meets x hx) hL (fits_small l hl mem)

end Johnson.G

#print axioms Johnson.G.linksSmallLit_meets
#print axioms Johnson.G.links_fit_small
#print axioms Johnson.G.links_john_small
#print axioms Johnson.G.fits_small
#print axioms Johnson.G.switch_ok_small
