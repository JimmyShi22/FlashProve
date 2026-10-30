-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinStdSpV.lean: under the hypotheses of `Spec.ldSpV_fresh`, for a batch: the mask of the
shared splitting, a free entry of a member of Ω's family, is fresh for sets of slots where the
closing of the test for linear constraints begins; and what the shared part reads there.

Definitions, statements (in `Cb.Spec`) and proofs. Generic: any `C : LdLinC`
(Cb/Ld/LdLinClosePre.lean), standard senders (Cb/Ld/LdLinStd.lean).
The closing of this test in this protocol's technical report (lean/CREDITS.md) begins with a
splitting by the shared part, whose mask κ is an entry of a mask-only member of Ω's family.
Cb/Ld/LdFrontV.lean (`frontV_sh`) has such a front for a batch; it asks a reading rd of the shared
witness, and that κ is fresh, for sets of slots, after what comes before. Under the hypotheses of
its statements, this file gives both, at the joint where the closing begins.

Main names:
  `Spec.ldSpV_put`: the splitting's overwriting of its entry is `Sig.ow` at that entry.
  `C.shMsg s`: the messages that the shared part holds, over the one signature `C.S`: G_u's
    family's and Ω's family's (mask-only members too), read off the shared witness `s : C.P.Sh6`; 0
    at the names of what a preamble left and of W's family, which belong to a slot.
  `C.rdV Rd pub s`: the reading: `C.shMsg s` cut to Rd; and pub of (what the shared part held
    before Ω's family was sent; the samples of Ω's family; ζ): any function: the record, the shared
    point, the locations with the folds read and ζ are among its arguments.
  `Spec.ldSpV_reads`: if Rd holds no entry of what a preamble left nor of W's family, and a slot's
    witness holds the shared families' pairs that s holds: `C.shMsg s` cut to Rd is the slot's
    messages cut to Rd.
  `Spec.ldSpV_fresh`: a nonempty ι, values of `C.P.X4` and `C.P.E4.Str`, `T.Places`, the layouts'
    conditions;
    κ := a free entry x₀ of a member of Ω's family, the splitting's entry
      (`⟨k.o, k.j⟩ = C.eO (T.YO.entF x₀)`; in the code the letter κ is a type);
    Rd holds κ and no pad entry of Ω's family
    ⇒ after (the core for a batch ; the step without rounds in every slot, `(C.link fq Bq).loV ..`)
      κ is fresh for sets of slots (in this sense: `ChainV.FreshForV`, Cb/Ld/LdLinChainVMask.lean),
      in the letters of `frontV_sh`'s last premise: shared reading `C.rdV Rd pub`, a slot's reading
      nothing; shared mask a scalar, overwriting `k.put`; no slot's mask.

Limits: narrower than the technical report in one point that this head declares: Rd holds no pad
entry of any member of Ω's family (Ω's own pad is withheld too). G_u's family, which is older, may
be read whole. Whether a second narrowing, which the head of Cb/Ld/LdLinChainVFresh.lean declares
under (2) ("the readings here forget the words as sent and the encoding randomness of the whole
family"), holds here too is not said.
What a slot may see beside: Cb/Ld/LdLinStdFresh.lean (`ldLinStdV_freshO`) has the finer fact after
the core. Here the slots' reading is cut to nothing, which is all that the shared splitting asks.
This file says nothing on the plan's ties and its public part, and nothing on soundness. That
layouts with these conditions exist is not said here.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinStdSp
import Cb.Ld.LdFrontVProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace LdLinC
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
  [Fintype Y] (C : LdLinC E ι κ J Y)

/-- The messages that the shared part holds, over the one signature. -/
def shMsgOf (mU : C.NU.Msg) (mO : C.NO.Msg) : C.S.Msg :=
  C.join4 (T := OMsg.Msg) (fun _ _ => 0) (fun _ _ => 0) mU mO
def shMsg (s : C.P.Sh6) : C.S.Msg := C.shMsgOf (C.NU.msgs s.1.1.1.2.2.2) (C.NO.msgs s.1.2.2.2)

/-- What the shared part reads where the closing begins. -/
def rdV (Rd : C.S.Ent → Prop) [DecidablePred Rd] {Xp : Type}
    (pub : C.P.Sh4 × C.NO.Smp × (Fin C.D.l → E) → Xp) (s : C.P.Sh6) : C.S.Msg × Xp :=
  (C.S.cut Rd (C.shMsg s), pub (s.1.1, s.1.2.1, s.2))

end LdLinC

namespace Spec

open Classical in
def ldSpV_put : Prop :=
  ∀ (E : Type) (S : Sig E) (G₁ G₂ : Grp S) (k : SplitAt G₁ G₂) (u : E) (m : S.Msg),
    k.put u m = S.ow (fun n => n = ⟨k.o, k.j⟩) (fun _ => u) m

section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

/-- Under the hypotheses below: on tied statements the shared part reads what the slots hold. -/
def ldSpV_reads : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (Rd : C.S.Ent → Prop) [DecidablePred Rd] (s : C.P.Sh6) (w : C.S.Wit),
    (∀ a j, ¬ Rd ⟨.inl (.inl (.inl a)), j⟩) → (∀ a j, ¬ Rd ⟨.inl (.inl (.inr a)), j⟩) →
    (∀ a, w (.inl (.inr a)) = s.1.1.1.2.2.2 a) → (∀ a, w (.inr a) = s.1.2.2.2 a) →
    C.S.cut Rd (C.shMsg s) = C.S.cut Rd (C.S.msgs w)

end

/-- Under the hypotheses below: the shared mask is fresh, for sets of slots, where the closing
begins. -/
def ldSpV_fresh (F E ι κ J Y : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (T : C.P.Std F) (LW : C.P.NW.O → ℕ) (LU : C.P.NU.O → ℕ)
      (LO : C.P.NO.O → ℕ) (tW : C.P.NW.O → ℕ) (tU : C.P.NU.O → ℕ) (tO : C.P.NO.O → ℕ)
      (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf N : ℕ) (qa : Finset C.P.Ea.Pos → Prop)
      (_ : C.P.X4) (_ : C.P.E4.Str) (G₁ G₂ : Grp C.S) (k : SplitAt G₁ G₂) (Rd : C.S.Ent → Prop)
      [DecidablePred Rd] (Xp : Type) (pub : C.P.Sh4 × C.NO.Smp × (Fin C.D.l → E) → Xp)
      (x₀ : Σ a, T.YO.Fr a) (Stq : Type) (fq : C.St6 → Stq)
      (Bq : IOR.Rels Unit Stq C.E₀ (C.S.Msg × C.Wpa))
      (tieB : C.P.Sh6 → Stq × C.S.Smp → (C.E₀.prod C.S.ext).Str → C.S.Wit × C.Wpa → Prop)
      (qB : QFam (C.E₀.prod C.S.ext) N),
    T.Places → T.YW.OK tW → T.YU.OK tU → T.YO.OK tO → (⟨k.o, k.j⟩ : C.S.Ent) = C.eO (T.YO.entF x₀) →
    Rd (C.eO (T.YO.entF x₀)) → (∀ n, Rd (C.eO n) → T.YO.NoPad n) →
    ((C.P.chainV (T.snd LW LU LO tW tU tO) qa N on0 εf).snoc
        ((C.link fq Bq).loV N (C.P.V6 (T.snd LW LU LO tW tU tO) qa N) tieB qB)).FreshForV
      (C.rdV Rd pub) (fun _ => ()) E (fun u κ' => (k.put u κ'.1, κ'.2)) Unit (fun _ κ' => κ')

end Spec

theorem ldSpV_put : Spec.ldSpV_put := by
  classical
  intro E S G₁ G₂ k u m
  funext a j
  by_cases hn : (⟨a, j⟩ : S.Ent) = ⟨k.o, k.j⟩
  · rw [ldk_ow_at _ _ _ a j hn]
    obtain ⟨ha, hj⟩ := Sigma.mk.inj_iff.1 hn
    subst ha
    have hj' : j = k.j := eq_of_heq hj
    subst hj'
    unfold SplitAt.put
    rw [Function.update_self, Function.update_self]
  · rw [ldk_ow_off _ _ _ a j hn]
    unfold SplitAt.put
    by_cases ha : a = k.o
    · subst ha
      rw [Function.update_self, Function.update_of_ne fun hj => hn (by rw [hj])]
    · rw [Function.update_of_ne ha]

section
variable {E ι κ J Y : Type}
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

omit [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
theorem ldSpV_reads : Spec.ldSpV_reads E ι κ J Y := by
  intro C Rd _ s w hA hW hU hO
  funext o j
  unfold Sig.cut
  rcases o with ((a | a) | a) | a
  · rw [if_neg (hA a j), if_neg (hA a j)]
  · rw [if_neg (hW a j), if_neg (hW a j)]
  · by_cases h : Rd ⟨.inl (.inr a), j⟩
    · rw [if_pos h, if_pos h]
      show (s.1.1.1.2.2.2 a).1 j = (w (.inl (.inr a))).1 j
      rw [hU a]
    · rw [if_neg h, if_neg h]
  · by_cases h : Rd ⟨.inr a, j⟩
    · rw [if_pos h, if_pos h]
      show (s.1.2.2.2 a).1 j = (w (.inr a)).1 j
      rw [hO a]
    · rw [if_neg h, if_neg h]

end

theorem ldSpV_fresh (F E ι κ J Y : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] :
    Spec.ldSpV_fresh F E ι κ J Y := by
  classical
  intro C T LW LU LO tW tU tO on0 εf N qa x₄ y₄ G₁ G₂ k Rd iRd Xp pub x₀ Stq fq Bq
    tieB qB hP hW hU hO hk h0 hR
  have hi : iRd = fun a => Classical.propDecidable (Rd a) := Subsingleton.elim _ _
  subst hi
  obtain ⟨⟨-, lO⟩, -, -, hdO⟩ := T.sndLaws LW LU LO hP hW hU hO
  -- after the core, with the parameters of the sender's law
  have f1 := ldLinV_freshO C.P on0 εf N (T.snd LW LU LO tW tU tO) qa x₄ y₄ E
    (T.YO.ownOne T.datO (fun w => w.2) (fun _ => 0, T.w3) x₀) _ _
    (fun m w' => (C.NO.cut (fun n => Rd (C.eO n)) m, w'))
    (fun u k' => (C.NO.ow (fun n => n = T.YO.entF x₀) (fun _ => u) k'.1, k'.2))
    (fun _ => ()) (fun _ _ => rfl)
    (stdL_ownOne F E C.P.NO T.YO tO C.P.W4 C.P.W3 T.datO (fun w => w.2) (fun _ => 0, T.w3)
      x₀ C.P.SdO (fun n => Rd (C.eO n)) hO hR h0)
    hdO lO (ldLinStd_apart C.P T LW LU LO tW tU tO)
  -- coarser readings
  have f2 := chainV_fresh_conseq Unit N _ _ _ _
    (C.P.chainV (T.snd LW LU LO tW tU tO) qa N on0 εf) _ _ _ _ _ _
    (fun z : (C.P.Sh4 × C.NO.Smp × (C.NO.Msg × C.P.W3)) × (Fin C.D.l → E) =>
      ((C.S.cut Rd (C.shMsgOf (C.NU.msgs z.1.1.1.2.2.2) z.1.2.2.1),
        pub (z.1.1, z.1.2.1, z.2)) : C.S.Msg × Xp))
    (fun _ => ()) E Unit _ _ (fun u κ' => (k.put u κ'.1, κ'.2))
    (fun _ κ' => κ') ?_ (fun _ _ => rfl) f1
  · have e : (fun s : C.P.Sh6 =>
          ((C.S.cut Rd
              (C.shMsgOf (C.NU.msgs s.1.1.1.2.2.2)
                (C.NO.cut (fun n => Rd (C.eO n)) (C.NO.msgs s.1.2.2.2))),
            pub (s.1.1, s.1.2.1, s.2)) : C.S.Msg × Xp)) =
        C.rdV Rd pub := by
      funext s
      refine Prod.ext (funext fun o => funext fun j => ?_) rfl
      show C.S.cut Rd _ o j = C.S.cut Rd (C.shMsg s) o j
      unfold Sig.cut
      rcases o with ((a | a) | a) | a
      · rfl
      · rfl
      · rfl
      · by_cases h : Rd ⟨.inr a, j⟩
        · rw [if_pos h, if_pos h]
          exact if_pos h
        · rw [if_neg h, if_neg h]
    refine (ChainV.freshForV_snoc _ _ _ _ E _ Unit _).2
      (Or.inr ⟨_, _, C.rdV Rd pub, fun _ => (), fun u κ' => (k.put u κ'.1, κ'.2),
          fun _ κ' => κ', e ▸ f2, ?_⟩)
    exact blindV_local _ _ _ _ (C.link fq Bq).R _ _ C.P.Sh6 (C.link fq Bq).H _ _ _ (C.rdV Rd pub)
      (fun _ => ()) (fun _ => ()) E Unit _ _ _
      (blind_stepPure _ _ _ _ _ _ (C.stepF fq) C.toE (C.stepM fq) _ _ (fun _ => ()) (fun _ => ())
        Unit (fun _ κ' => κ') (fun _ κ' => κ') fun _ _ _ _ _ => ⟨rfl, rfl⟩)
  · intro u z
    refine Prod.ext ?_ rfl
    show C.S.cut Rd (C.shMsgOf _ (C.NO.ow (fun n => n = T.YO.entF x₀) (fun _ => u) z.1.2.2.1)) =
      k.put u (C.S.cut Rd (C.shMsgOf _ z.1.2.2.1))
    rw [ldSpV_put, hk]
    funext o j
    by_cases hn : (⟨o, j⟩ : C.S.Ent) = C.eO (T.YO.entF x₀)
    · rw [ldk_ow_at _ _ _ o j hn]
      unfold Sig.cut
      rw [if_pos (hn ▸ h0)]
      obtain ⟨ho, hj⟩ := Sigma.mk.inj_iff.1 hn
      subst ho
      have hj' : j = (T.YO.entF x₀).2 := eq_of_heq hj
      subst hj'
      exact ldk_ow_at (N := C.NO) (fun n => n = T.YO.entF x₀) (fun _ => u) z.1.2.2.1
        (T.YO.entF x₀).1 (T.YO.entF x₀).2 rfl
    · rw [ldk_ow_off _ _ _ o j hn]
      unfold Sig.cut
      rcases o with ((a | a) | a) | a
      · rfl
      · rfl
      · rfl
      · have hn' : ¬ ((⟨a, j⟩ : C.NO.Ent) = T.YO.entF x₀) := fun h' => hn (congrArg C.eO h')
        by_cases h : Rd ⟨.inr a, j⟩
        · rw [if_pos h, if_pos h]
          exact ldk_ow_off (N := C.NO) (fun n => n = T.YO.entF x₀) (fun _ => u) z.1.2.2.1 a j hn'
        · rw [if_neg h, if_neg h]

end Cb
