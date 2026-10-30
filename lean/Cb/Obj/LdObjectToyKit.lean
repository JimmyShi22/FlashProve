-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectToyKit.lean: for toys first: a standard oracle message with its sender, and two laws
of code complexes.

In standard terms: lemmas for building example instances: a simple encoded prover message (data
entries and one pad entry under any code, with its sample map) and its honest sender.

Definitions, statements and proofs. A tool for guards against empty theorems; no parameter of a
protocol; used beyond guards too, among others: `ld_dist_fam` is used in `ldThird_bridge`
(Cb/Ld/LdTowerThird.lean) and `ldJohn_bridge` (Cb/Ld/LdTowerJohn.lean), both laws in `glC_code`
(Cb/Gl/GlLd.lean), and `StdM` is the form of the messages that Cb/Ld/LdBldMsg.lean builds
(`BldM.M`). Codes: `LdCode`, Cb/Ld/LdRel.lean; oracle messages: `OMsg`, Cb/Ld/LdSig.lean.

Why a file of its own: over a concrete field Lean must not compare numbers by unfolding. So what a
toy needs is stated and proved here for an abstract finite field and a variable code, with the
needed facts as hypotheses; a toy only instantiates.

Main names:
  `ld_dist_fam`, `ld_transp_fam`: a complex (`LdCode.fam`, Cb/Ld/LdRel.lean) of codes with distance
    d has distance d; of transparent codes is transparent.
  `StdM E P`: a code Cm read at long positions P; its message has the entries Dt (data) and one pad
    entry, named by place; each datum has a corner of a cube (plc); the values b of the pad's
    coefficient; a radius.
  `M.OK L t` asks, among other things, that no two data have the same corner and that b is never 0.
  `M.Z`: the sample, which is the row with a pad of Cb/Gen/OodDecPad.lean (equality weights at a
    point on the data, β on the pad).
  `M.snd dat`: the sender; the data are dat of the witness, the coin that goes into the message is
    the pad.
  Under `h : M.OK L t`, `stdM_list`, `stdM_evades`, `stdM_uniform`, `stdM_blind`, `stdM_hides`:
    lists from the code's; two different messages of one list agree at no more than `M.Z.err`
    seeds; the answer is uniform at every seed; so its law does not depend on the witness; the
    encoding hides what the code's does.

`D.Blind Sd` (`Sig.Sender.Blind`) asks that, for every joint seed s and all witnesses w and w', the
distribution of `D.ans Sd s w k` over uniform k in `D.Mk` equal that of `D.ans Sd s w' k`;
`D.ans Sd s w k` gives the family, over the members a, of the answers `(N.om a).Z.val (Sd.sd a s)`
of `D.upM (D.put w k) a`, and the distribution is of that whole family. For one oracle message o,
`D.Blind` (`OMsg.Sender.Blind`) asks the same with a seed ρ of `o.Z` in place of s: that, for every
ρ and all w and w', the distribution of `D.ans ρ w k` over uniform k in `D.Mk` equal that of
`D.ans ρ w' k`, where `D.ans ρ w k` is `o.Z.val ρ (D.upM (D.put w k))`. Here `OMsg.Sender.Blind`
(Cb/Ld/LdSend.lean) is a conclusion (`stdM_blind`, under `h : M.OK L t`).

Notation: `L`: a natural number (`M.OK L t` says that it bounds the lists of the code at the radius
`M.e`); `μ`: a type (the cube's coordinates: `plc : Dt → μ → Bool`); `B`: a type (`b : B → E` gives
the values of the pad's coefficient).

Limits: the standard oracle message is no proposal for a protocol; this file fixes no value of
`StdM`, which is the form of an oracle message in Cb/Ld/LdBldMsg.lean (`BldM.M`).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSendProofs
import Cb.Ld.LdSendMem
import Cb.Ld.LdSigProofs
import Cb.Ld.LdRelProofsCode

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood

/-! ## Complexes -/

section Fam
variable {E P : Type} [Field E]

theorem ld_dist_fam [Fintype P] {A : Type} [Fintype A] [DecidableEq A] (C : A → LdCode E P)
    (d : ℕ) (h : ∀ a, (C a).Dist d) : (LdCode.fam C).Dist d := by
  intro m r hne
  have : ∃ a, ¬ ((fun j => m ⟨a, j⟩) = 0 ∧ (fun q => r ⟨a, q⟩) = 0) := by
    by_contra hn
    have hn' : ∀ a, (fun j => m ⟨a, j⟩) = 0 ∧ (fun q => r ⟨a, q⟩) = 0 := fun a =>
      by_contra fun ha => hn ⟨a, ha⟩
    exact hne ⟨funext fun n => congrFun (hn' n.1).1 n.2, funext fun n => congrFun (hn' n.1).2 n.2⟩
  obtain ⟨a, ha⟩ := this
  exact le_trans (h a _ _ ha) (cnt_mono fun x hx hh => hx (funext fun α => congrFun hh ⟨a, α⟩))

omit [Field E] in
theorem ld_transp_fam {A : Type} [Fintype A] [DecidableEq A]
    (C : A → LdCode E P) (h : ∀ a, (C a).Transparent) : (LdCode.fam C).Transparent := by
  choose bk hbk using h
  exact ⟨fun x g p => bk p.1 x (fun α => g ⟨p.1, α⟩) p.2,
    fun m r x p hp =>
      hbk p.1 (fun j => m ⟨p.1, j⟩) (fun q => r ⟨p.1, q⟩) x p.2 (Finset.mem_sigma.1 hp).2⟩

end Fam

/-! ## A standard oracle message -/

/-- A standard oracle message: the data. -/
structure StdM (E P : Type) [Fintype P] where
  Cm : LdCode E P
  Dt : Type
  [finDt : Fintype Dt]
  place : Dt ⊕ Unit ≃ Cm.J
  μ : Type
  [finμ : Fintype μ]
  [decμ : DecidableEq μ]
  plc : Dt → μ → Bool
  B : Type
  [finB : Fintype B]
  [neB : Nonempty B]
  b : B → E
  e : ℕ

attribute [instance] StdM.finDt StdM.finμ StdM.decμ StdM.finB StdM.neB

namespace StdM
variable {E P : Type} [Fintype P] [Field E] [Fintype E] (M : StdM E P)

/-- the row with a pad, on data and pad -/
@[reducible] def Z₀ : Sample E (M.Dt ⊕ Unit) :=
  Sample.pad E M.μ M.Dt Unit M.B M.plc (fun _ => 1) M.b

/-- The sample, on the entries of the message. -/
@[reducible] def Z : Sample E M.Cm.J := M.Z₀.comap M.place.symm

/-- The oracle message. -/
@[reducible] def om : OMsg E := OMsg.plain M.Cm M.Z M.e fun _ => 0

/-- The sender. -/
@[reducible] def snd {W : Type} (dat : W → M.Dt → E) (w0 : W) : M.om.Sender W Unit where
  N := M.Cm.Nn
  upM := fun m => m
  upR := fun r => r
  Mk := E
  put := fun w k j => Sum.elim (dat w) (fun _ => k) (M.place.symm j)
  rest := fun _ => ()
  w0 := w0

/-- what is asked of the data -/
structure OK (L t : ℕ) : Prop where
  laws : M.Cm.Laws
  list : M.Cm.ListAt M.e L
  zk   : M.Cm.Zk t
  plc  : Function.Injective M.plc
  inj  : Function.Injective M.b
  ne0  : ∀ β, M.b β ≠ 0

end StdM

section
variable {E P : Type} [Fintype P] [Field E] [Fintype E] (M : StdM E P)

omit [Fintype E] in
theorem std_padBasis : PadBasis E (fun _ : Unit => (1 : E)) := by
  have h : ∀ c : Unit → E, padVal (F := E) (fun _ : Unit => (1 : E)) c = c () :=
    fun c => by simp [padVal]
  exact ⟨fun c c' hc => funext fun _ => by rw [← h c, ← h c', hc], fun y => ⟨fun _ => y, h _⟩⟩

theorem stdM_list {L t : ℕ} (h : M.OK L t) : M.om.ListLE L := sig_list_of_code E M.om L h.list

theorem stdM_evades {L t : ℕ} (h : M.OK L t) : M.om.Evades :=
  sig_evades_of_okOn E M.om _
    (ood_okOn_comap E (M.Dt ⊕ Unit) M.Cm.J M.Z₀ M.place.symm (PadInF E)
      (ood_okOn_pad E E M.μ M.Dt Unit M.B _ _ _ h.plc h.inj std_padBasis.1))
    fun _ _ _ _ _ _ => ⟨_, rfl⟩

theorem stdM_enc {W : Type} (dat : W → M.Dt → E) (w0 : W)
    (m : (M.snd dat w0).N.Msg) (r : (M.snd dat w0).N.Rnd) :
    M.om.upW ((M.snd dat w0).N.enc m r) =
      M.om.C.enc ((M.snd dat w0).upM m) ((M.snd dat w0).upR r) := rfl

/-- the message holds the data at their places -/
theorem stdM_put {W : Type} (dat : W → M.Dt → E) (w0 : W) (w : W) (k : E) (i : M.Dt) :
    (M.snd dat w0).upM ((M.snd dat w0).put w k) (M.place (Sum.inl i)) = dat w i := by
  show Sum.elim (dat w) (fun _ => k) (M.place.symm (M.place (Sum.inl i))) = dat w i
  rw [Equiv.symm_apply_apply]
  rfl

theorem stdM_comap : M.Z.comap M.place = M.Z₀ := by
  show ({ D := M.Z₀.D, S := M.Z₀.S, mat := fun ρ s n => M.Z₀.mat ρ s (M.place.symm (M.place n)),
          err := M.Z₀.err } : Sample E (M.Dt ⊕ Unit)) = M.Z₀
  simp only [Equiv.symm_apply_apply]

theorem stdM_uniform {L t : ℕ} (h : M.OK L t) {W : Type} (dat : W → M.Dt → E) (w0 : W) :
    (M.snd dat w0).Uniform := by
  refine ldSend_uniform_of_private E E M.om W Unit (M.snd dat w0) M.Dt Unit Unit M.place.symm
    ⟨fun k => ((), fun _ => k), fun x => x.2 (), fun _ => rfl, fun _ => rfl⟩
    (fun w _ => dat w) ?_ ?_
  · intro w k n
    show Sum.elim (dat w) (fun _ => k) (M.place.symm (M.place.symm.symm n)) = _
    rw [Equiv.symm_symm, Equiv.symm_apply_apply]
    rcases n with _ | _ <;> rfl
  · show (M.Z.comap M.place.symm.symm).Private E fun _ => True
    rw [Equiv.symm_symm, stdM_comap]
    exact fun ρ _ a => ood_private_pad E E M.μ M.Dt Unit M.B _ _ _ std_padBasis ρ (h.ne0 ρ.2) a

theorem stdM_blind {L t : ℕ} (h : M.OK L t) {W : Type} (dat : W → M.Dt → E) (w0 : W) :
    (M.snd dat w0).Blind :=
  ldSend_blind_of_uniform E M.om W Unit (M.snd dat w0) (stdM_uniform M h dat w0)

theorem stdM_hides {L t : ℕ} (h : M.OK L t) {W : Type} (dat : W → M.Dt → E) (w0 : W) :
    (M.snd dat w0).N.Hides (M.om.C.budT t) := h.zk

end
end Cb
