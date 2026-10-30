-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/MadeAtHear.lean: code switching (K2): FOUR OF THE SIX MAKINGS THAT ITS SHARE OF e₁
AT «H:2» (sub-protocol number 339) ASKS (hMade, Johnson/P1K2R/SharesAtE.lean): THE PUBLIC ITEMS
«ledger 24» · «freeAbove 24» · «linkFresh 24» · «lookIn 24 3» HOLD BEHIND EVERY ACCEPT OF THE
LOT's OWN SUB-PROTOCOL THERE, in hMade's own letters. A JOIN. NO BLOCK IMPORTS THIS FILE.
  made_hear   at every accept s ↦ s' from an unmarked state at which the promise's tests in front
              hold to an unmarked state: the four
PREMISES, NAMED, NOT SHOWN: ON THE PLAN, at the head's link's letters HP (ProofFile.pureLetters G₀ 24):
hns: the plan's number of slots of segment 24 (D.nsOf 24) is HP.hp.ns · hB: the one
Bool madeLookB accepts at HP's letters · ON THE STATE IN FRONT: hU: the head's own part has
nothing heard at either seat (Tw/K2C/HeadUnheard.lean | HeadUnheardReached.lean are
its payers).
THE LOT's OTHER DRESS AT THAT PLACE (a link's) accepts no state at which the promise's tests in
front hold: P1K2.hands_head_other stands at EVERY E: laid here at an E whose value behind is the
sentence wanted. BY: P1K2.made_ledger_sits (Johnson/P1K2R/MadeLedger.lean) · K2.made_head
(Tw/K2C/MadeLook.lean) · sits_under_head | sits_under_link · K2.k2_step_two · P1K2.letters_l.
LIMITS. hMade IS NOT PAID ("frame.sentIs" · "ledger.treesAre" are left at 339). No soundness is
claimed.
-/
import Johnson.P1K2R.MadeLookAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open VerifiableInference.Desc (Block Place OpenedColumn KindName)
open VerifiableInference.Desc.First (S ModelPart Numbers Pub PubData pubAll)
open VerifiableInference.Desc.First.K2 (HeadPar k2_step_two made_head madeLookB)
open H2K.JointK (Sits)
open ProofFile (Cl)
open IM (Hands XK Yes linksW placesW k2P)

variable {P : Type}

theorem made_hear {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {b' : Block S Cl}
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some 24, piece := 2, kind := .K2 })
    (D : PubData) (base : Pub → P × S → Bool) (z : P)
    (hns : ∀ HP, pureLetters G₀ 24 = some HP → D.nsOf 24 = some HP.hp.ns)
    (hB : ∀ HP, pureLetters G₀ 24 = some HP →
      madeLookB D.d3 24 3 HP.X.arrayOf 0 HP.hp.ns = true)
    {N : Numbers} {E : Nat → S → Bool} {ft : Nat} {s s' : S} (hy : Yes ft b' s s')
    (hu : s.failed = none) (hu' : s'.failed = none)
    (hx : XK N linksW placesW E 339 s = true)
    (hU : ∀ a, s.here = .head a → a.tl.heard = none ∧ a.lookHeard = none) :
    (pubAll D base (.ledger 24) (z, s') = true ∧ pubAll D base (.freeAbove 24) (z, s') = true) ∧
      pubAll D base (.linkFresh 24) (z, s') = true ∧
      pubAll D base (.lookIn 24 3) (z, s') = true := by
  obtain ⟨L, hL, hb'⟩ := hlot
  obtain ⟨x, hx', rfl⟩ := IM.lot_K2 hL hb' (by rw [hpl])
  have hi := IM.k2_mem hx'
  rw [show x.place = _ from hpl] at hi
  rcases hi with ⟨_, hm⟩ | ⟨Pp, n, _, _, hA⟩
  · exact absurd hy (never_of_mute hm s s')
  · rcases hA with ⟨h0, _⟩ | ⟨l, HP, hl, hHP, hxe⟩ | ⟨l, _, hxe⟩
    · cases h0
    · obtain rfl : 24 = l := Option.some.inj hl
      have hS := sits_under_head x.name
        { chain := 1, link := some 24, piece := 2, kind := .K2 }
        (k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name .head n) HP
      rw [← hxe] at hS
      refine ⟨made_ledger_sits hS D base z (hns HP hHP) hy, ?_⟩
      obtain ⟨rs, cols, k, e⟩ := hy
      obtain ⟨t, t', e1, e2, e3⟩ := hS.step ft s s' rs cols k e
      obtain rfl : s = t := Except.ok.inj e1
      obtain ⟨r₁, r₂, gs, _, hdc⟩ := k2_step_two e2
      have hl24 : HP.l = 24 := letters_l hHP
      have h4 := made_head D base z (pc := 3) (P := HP) rfl (by rw [hl24]; exact hB HP hHP) hU
        hdc e3
      rw [hl24] at h4
      exact h4
    · have hS := sits_under_link x.name
        { chain := 1, link := some 24, piece := 2, kind := .K2 }
        (k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name .link n)
      rw [← hxe] at hS
      have H := hands_head_other rfl hS door_bare_link (N := N)
        (E := fun j t => if j = 339 + 1 then
          ((pubAll D base (.ledger 24) (z, t) && pubAll D base (.freeAbove 24) (z, t)) &&
            (pubAll D base (.linkFresh 24) (z, t) && pubAll D base (.lookIn 24 3) (z, t)))
          else E j t) (ft := ft)
      have hx2 := H.more s s' hy hu hu' (by
        rw [xk_same (E := E)]
        · exact hx
        · exact if_neg (by omega))
      rw [if_pos rfl] at hx2
      simp only [Bool.and_eq_true] at hx2
      exact hx2

end P1K2

#print axioms P1K2.made_hear
