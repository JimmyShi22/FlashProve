-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/MadeLookAt.lean: code switching (K2): TWO MORE OF THE MAKINGS THAT ITS SHARES OF e₁
ASK (hMade, Johnson/P1K2R/SharesAtE.lean): THE PUBLIC ITEMS «linkFresh l» AND «lookIn l 2» HOLD
BEHIND EVERY ACCEPT OF A LINK's FIRST PLACE (1 ≤ l < 24), in hMade's own letters. A JOIN of
Johnson/Top/H0/Tw/K2C/MadeLook.lean with the place's own steps. NO BLOCK IMPORTS
THIS FILE.
  xk_same           the promise's tests at border k read the further Bools E at k alone
  made_look_first   at every accept s ↦ s' of the sub-protocol at the link's first place, from an
                    unmarked state at which the promise's tests in front hold to an unmarked
                    state: pubAll D base (.linkFresh l) (z, s') = true ∧ pubAll D base (.lookIn l
                    2) (z, s') = true
PREMISES ON THE PLAN, NAMED, NOT SHOWN: hsub (the driver's list has the written sort at l: in
scope: P1K2.subs_W) · hBA | hBL: at the attention table's | the layers' plan of the link: the
one Bool madeLookB (MadeLook.lean) accepts at the frame's letters, and the plan's state of the
smallness test has nothing heard.
THE LOT's OTHER DRESS AT SUCH A PLACE (the head's) accepts no state at which the promise's tests
in front hold: P1K2.hands_link_other stands at EVERY E: laid here at an E whose value behind is
the sentence wanted. BY: made_lay | made_att (MadeLook.lean) · IM.lot_K2 | k2_mem · sits_of_joined
· sitsJoined_keeps · leaveOpened_is · K2.k2_step_two · framesOf_arms ·
P1K2.kinds_of_subs.
LIMITS. hMade IS NOT PAID (two of its six | eight items, at the 23). No soundness is claimed.

-/
import Johnson.P1K2R.MadeLedger
import Johnson.Top.H0.Tw.K2C.MadeLook

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open VerifiableInference.Desc (Block Place OpenedColumn KindName)
open VerifiableInference.Desc.First (S ModelPart Numbers Pub PubData pubAll)
open VerifiableInference.Desc.First.K2 (k2_step_two made_lay made_att madeLookB)
open Johnson.Desc.First.Walk.Seat (framesOf_arms pubOf)
open H2K.JointK (Sits)
open ProofFile (Cl)
open IM (Hands XK BK Yes linksW placesW subW k2P Joined)

variable {P : Type}

theorem xk_same {N : Numbers} {links : List ModelPart} {ps : List Place} {E E' : Nat → S → Bool}
    {k : Nat} {s : S} (h : E' k s = E k s) : XK N links ps E' k s = XK N links ps E k s := by
  unfold XK
  rw [h]

theorem made_look_first {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24)
    {b b' : Block S Cl} (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some l, piece := 1, kind := .K2 })
    (hJ : Joined Z l b b' { chain := 1, link := some l, piece := 1, kind := .K2 })
    (hsub : (ProofFile.subsOf Z)[l]? = some (subW l))
    (D : PubData) (base : Pub → P × S → Bool) (z : P)
    (hBA : ∀ X p, Z.p.built.links[l]? = some X → X.kind = 1 → Z.p.X.A[X.g]? = some p →
      madeLookB D.d3 l 2 (pubOf X).arrayOf (pubOf X).Fp.next p.ns = true ∧
        p.seam.tl.heard = none)
    (hBL : ∀ X hp, Z.p.built.links[l]? = some X → X.kind = 0 → Z.p.X.G[X.g]? = some hp →
      madeLookB D.d3 l 2 (pubOf X).arrayOf (pubOf X).Fp.next hp.ns = true ∧
        hp.tl.heard = none)
    {N : Numbers} {E : Nat → S → Bool} {ft : Nat} {s s' : S} (hy : Yes ft b s s')
    (hu : s.failed = none) (hu' : s'.failed = none)
    (hx : XK N linksW placesW E (14 * l + 2) s = true) :
    pubAll D base (.linkFresh l) (z, s') = true ∧ pubAll D base (.lookIn l 2) (z, s') = true := by
  obtain ⟨L, hL, hb'⟩ := hlot
  obtain ⟨x, hx', rfl⟩ := IM.lot_K2 hL hb' (by rw [hpl])
  have hi := IM.k2_mem hx'
  rw [show x.place = _ from hpl] at hi
  rcases hi with ⟨_, hm⟩ | hd
  · obtain ⟨rs, cols, n, e⟩ := hy
    obtain ⟨fs, f, m, _, _, e3, _⟩ := hJ.step e
    exact absurd ⟨rs, cols, n, e3⟩ (never_of_mute hm s m)
  · obtain ⟨fs, f, hfs, hf, hSJ⟩ := sits_of_joined hJ (fun e => by cases e) rfl hd
    obtain ⟨Pp, n, _, _, hA⟩ := sitsJoined_keeps hfs hf hSJ
    rcases hA with ⟨l', HP, _, _, hS, _⟩ | ⟨l', _, hS, _⟩
    · have H := hands_link_other h1 h24 rfl hS (door_head_opened f HP).mark (N := N)
        (E := fun j t => if j = 14 * l + 2 + 1 then
          (pubAll D base (.linkFresh l) (z, t) && pubAll D base (.lookIn l 2) (z, t))
          else E j t) (ft := ft)
      have hx2 := H.more s s' hy hu hu' (by
        rw [xk_same (E := E)]
        · exact hx
        · exact if_neg (by omega))
      rw [if_pos rfl, Bool.and_eq_true] at hx2
      exact hx2
    · obtain ⟨rs, cols, k, e⟩ := hy
      obtain ⟨t, t', e1, e2, e3⟩ := hS.step ft s s' rs cols k e
      obtain ⟨r₁, r₂, gs, _, hdc⟩ := k2_step_two e2
      have ho := leaveOpened_is e3
      obtain ⟨X₀, hX₀, hk₀, _, _⟩ := kinds_of_subs h24 hsub
      rcases framesOf_arms hfs hf with ⟨X, hX, hk, _⟩ | ⟨h0, _⟩ |
        ⟨_, X, p, Q, hX, hk, hA', hQ, _, eo, _⟩ | ⟨_, X, hp, Q, hX, hk, hG, hQ, _, eo, _⟩
      · obtain rfl : X₀ = X := Option.some.inj (hX₀.symm.trans hX)
        exact absurd hk hk₀
      · omega
      · rw [eo] at ho
        subst hQ
        obtain ⟨hB, hh⟩ := hBA X p hX hk hA'
        exact made_att D base z (pc := 2) hB hh hdc ho
      · rw [eo] at ho
        subst hQ
        obtain ⟨hB, hh⟩ := hBL X hp hX hk hG
        exact made_lay D base z (pc := 2) hB hh hdc ho

end P1K2

#print axioms P1K2.xk_same
#print axioms P1K2.made_look_first
