-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Sub/LateJoin.lean: the chain in front of a late message and the block that proves agreement, in a
row; and the rule of Cb/Sub/Acc.lean for a meaning that reads the statement's other part too.

Definitions, statements and their proofs.
The verifier keeps ONE ledger LS, on early and late entries (J₁ ⊕ J₂). The weights `a x'` along
which a late entry is an affine form in the early ones are read off the public statement. In front
of the block that proves agreement the ledger's MEANING is its pull-back (`virtJ`), for each fixed
tuple of early messages. That block starts from the ledger read as it stands, of early and late
entries, and agreement (`realJ`), for each fixed tuple of early and late messages. `late_join` lays
the two in a row.

Main names:
  `bothJ A Q P`: a joint beside a carried value whose meaning Q reads the statement's other part.
  `acc_red_out`: what `R.acc upd` puts out.
  `acc2_knowAt`: the rule of `acc_knowAt` (Cb/Sub/Acc.lean) at such joints; its last premise may use
    that the new statement is R's output at the old one.
  `virtJ B₀ a msg₁ n`, `realJ B₀ a msg₁ ent n`: the two joints on (public data, LS).
  `late_join`: `KnowAt R A (virtJ ..)` at the early tuples and `KnowAt T (realJ ..) C` at the tuples
    (early, late) give `KnowAt (R.seq T) (comapM Prod.fst A) C`, errors in a row.

Limits: nothing on an honest prover. No block is given.
THE CONCLUSION OF `late_join` IS "FOR EACH FIXED TUPLE (EARLY, LATE)": IT HOLDS THE LATE MESSAGE
FIXED FROM THE FIRST ROUND OF R ON. It is a statement on the two blocks' relations. It does NOT say
that a prover who picks the late message behind R's challenges is caught: to pass from it to oracle
messages by `sigLift_know` over a signature that holds the late message would describe a protocol in
which that message is sent at the start. What speaks for the true order is in the premises alone:
R's own `KnowAt` is at the early tuples, so its bad challenges do not hang on the late message. The
join in the true order (R over the early signature, the sending of the late message, T over both) is
not written here.
That the weights are fixed before the late message is sent is not said by any type here either.
Terms: lean/GLOSSARY.md.
-/
import Cb.Sub.Acc
import Cb.Sub.Late

set_option autoImplicit false

namespace Cb.Sub
open Iop Prob Hiop TWhole IOR

/-- A joint beside a carried value whose meaning reads the statement's other part too. -/
def bothJ {K X Z W : Type} {Ex : ExtSpec} (A : Rels K X Ex W) (Q : X → Z → W → Prop)
    (P : Z → Prop) : Rels K (X × Z) Ex W :=
  ⟨fun x y w => A.rel x.1 y w ∧ Q x.1 x.2 w, fun a w => A.relR (a.1.1, a.2) w ∧ Q a.1.1 a.1.2 w,
    fun a => A.on (a.1.1, a.2) ∧ P a.1.2, A.core⟩

/-- What a block beside a carried value puts out. -/
theorem acc_red_out {X X' Z : Type} {Ei Eo : ExtSpec} (R : IOR X Ei X' Eo) (upd : X' → Z → Z)
    (a : (X × Z) × Ei.Str) (τ : Tr R.shape) (b : (X' × Z) × Eo.Str)
    (hb : (R.acc upd).red.out a τ = some b) :
    R.red.out (a.1.1, a.2) τ = some (b.1.1, b.2) ∧ b.1.2 = upd b.1.1 a.1.2 := by
  obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
  obtain ⟨xz, hxz, hf⟩ := Option.bind_eq_some_iff.1 h1
  have hk : (R.keepX Z).red.out a τ = some (xz, (R.keepX Z).imp a.2 τ) :=
    red_out_eq_some.2 ⟨hxz, rfl⟩
  obtain ⟨k1, k2⟩ := keepX_red_out R Z a τ _ hk
  have e : b.1 = (xz.1, upd xz.1 xz.2) := (Option.some.inj hf).symm
  have e1 : b.1.1 = xz.1 := by rw [e]
  have e2 : b.1.2 = upd xz.1 xz.2 := by rw [e]
  refine ⟨?_, ?_⟩
  · rw [e1, h2]
    exact k2
  · rw [e2, e1]
    exact congrArg (upd xz.1) k1

/-- A block beside a carried value, the meaning reading the statement's other part. -/
theorem acc2_knowAt {K M X X' Z Wp : Type} {Ei Eo : ExtSpec} {R : IOR X Ei X' Eo}
    {A : Rels K X Ei (M × Wp)} {B B₀ : Rels K X' Eo (M × Wp)} {ε : Err R.shape}
    (upd : X' → Z → Z) (Q : X → Z → M × Wp → Prop) (Q' : X' → Z → M × Wp → Prop) (P P' : Z → Prop)
    (h : KnowAt R A B idW ε) (ho : ∀ b, B.on b → B₀.on b) (hP : ∀ x' z, P z → P' (upd x' z))
    (hB : ∀ a τ b z w, A.on a → R.red.out a τ = some b → P z → B₀.relR b w →
      Q' b.1 (upd b.1 z) w → B.relR b w ∧ Q a.1 z w) :
    KnowAt (R.acc upd) (bothJ A Q P) (bothJ B₀ Q' P') idW ε where
  point := h.point
  isLocal := (isLocal_keepX h.isLocal Z).post _ _ (extMap_isLocal.1 Eo)
  onOut := fun a τ b ha hb => by
    obtain ⟨h1, h2⟩ := acc_red_out R upd a τ b hb
    exact ⟨ho _ (h.onOut (a.1.1, a.2) τ (b.1.1, b.2) ha.1 h1), h2 ▸ hP b.1.1 a.1.2 ha.2⟩
  know := fun m a ha =>
    Doomed.mono _ _ (fun τ hτ b w hb hw => by
      obtain ⟨h1, h2⟩ := acc_red_out R upd a τ b hb
      have hq : Q' b.1.1 (upd b.1.1 a.1.2) (m, w) := h2 ▸ hw.2
      obtain ⟨g1, g2⟩ := hB (a.1.1, a.2) τ (b.1.1, b.2) a.1.2 (m, w) ha.1 h1 ha.2 hw.1 hq
      exact ⟨hτ (b.1.1, b.2) w h1 g1, g2⟩) (h.know m (a.1.1, a.2) ha.1)

section Late
variable {E J₁ J₂ : Type} [Field E] [Fintype J₁] [Fintype J₂]

/-- In front of the block that proves agreement: B₀, and the ledger's pull-back holds of the early
entries. -/
def virtJ {K X M Wp : Type} {Ex : ExtSpec} (B₀ : Rels K X Ex (M × Wp)) (a : X → J₂ → Aff E J₁)
    (msg₁ : M → J₁ → E) (n : ℕ) : Rels K (X × Ledger E (J₁ ⊕ J₂)) Ex (M × Wp) :=
  bothJ B₀ (fun x L w => Ledger.Holds (pullL (a x) L) (msg₁ w.1)) fun L => L.length ≤ n

/-- Where that block starts: B₀, agreement, and the ledger holds of the early and late entries. -/
def realJ {K X M U Wp : Type} {Ex : ExtSpec} (B₀ : Rels K X Ex (M × Wp)) (a : X → J₂ → Aff E J₁)
    (msg₁ : M → J₁ → E) (ent : U → J₂ → E) (n : ℕ) :
    Rels K (X × Ledger E (J₁ ⊕ J₂)) Ex ((M × U) × Wp) :=
  bothJ (comapM Prod.fst B₀)
    (fun x L w => Agree (a x) (msg₁ w.1.1) (ent w.1.2) ∧
      Ledger.Holds L (Sum.elim (msg₁ w.1.1) (ent w.1.2))) fun L => L.length ≤ n

/-- The seam's algebra, for each fixed tuple (early, late). The late message is held fixed
from R's first round on: this is NOT the theorem on a prover that picks it behind R's challenges:
that is `late_true_order` (Cb/Sub/TrueOrder.lean). See this file's head. -/
theorem late_join {K X X' X'' M U Wp : Type} {E₁ E₂ E₃ : ExtSpec}
    {R : IOR X E₁ (X' × Ledger E (J₁ ⊕ J₂)) E₂} {T : IOR (X' × Ledger E (J₁ ⊕ J₂)) E₂ X'' E₃}
    {A : Rels K X E₁ (M × Wp)} {B₀ : Rels K X' E₂ (M × Wp)} {C : Rels K X'' E₃ ((M × U) × Wp)}
    {ε₁ : Err R.shape} {ε₂ : Err T.shape} (a : X' → J₂ → Aff E J₁) (msg₁ : M → J₁ → E)
    (ent : U → J₂ → E) (n : ℕ) (h₁ : KnowAt R A (virtJ B₀ a msg₁ n) idW ε₁)
    (h₂ : KnowAt T (realJ B₀ a msg₁ ent n) C idW ε₂) :
    KnowAt (R.seq T) (comapM (M' := M × U) Prod.fst A) C idW (Err.app ε₁ ε₂) :=
  knowAt_seq
    (knowAt_mono (comapM_knowAt (M' := M × U) Prod.fst h₁) (fun _ ha => ha) (fun _ _ _ hw => hw)
      (B' := realJ B₀ a msg₁ ent n)
      (fun b w _ (hw : B₀.relR (b.1.1, b.2) (w.1.1, w.2) ∧
          Agree (a b.1.1) (msg₁ w.1.1) (ent w.1.2) ∧
          Ledger.Holds b.1.2 (Sum.elim (msg₁ w.1.1) (ent w.1.2))) =>
        (⟨hw.1, (late_holds (a b.1.1) b.1.2 (msg₁ w.1.1) (ent w.1.2) hw.2.1).1 hw.2.2⟩ :
          B₀.relR (b.1.1, b.2) (w.1.1, w.2) ∧
            Ledger.Holds (pullL (a b.1.1) b.1.2) (msg₁ w.1.1)))
      fun _ hb => hb) h₂

end Late
end Cb.Sub
