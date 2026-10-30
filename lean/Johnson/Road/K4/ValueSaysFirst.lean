-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/ValueSaysFirst.lean: WHAT IS CLAIMED BEFORE THE FIRST ROUND OF THE CHAIN OF THE
FIRST LAYERS' SUB-PROOF's OWN ROUNDS (g = 0), AT THE VALUE OF Johnson/Road/K4/CarriageFirst.lean
(`Plan4F.fullF`), WRITTEN OUT IN THE VALUE's OWN LETTERS. The twin of
Johnson/Road/K4/ValueSays.lean. A definition and one theorem: by `ownF_pT`
(Cb/Pv/Lay/At/OwnFirstW.lean), `jn_iff` (Cb/Pv/Lay/At/Fore.lean), `emb_zero`
(Cb/Pv/Lay/EmbSide.lean) and `Plan4.kEnd_eq` (ValueSays.lean).

  `Plan4F.J11 x m`: the library's identity (J11) at every feature below d and every position below
    2 ^ lT: the entry of the stream that comes in is the entry, at that feature, of the row of the
    committed embedding (`embR`, read off the committed matrix) at the token `Q.tok x p`.
  `Plan4F.pTF_iff`: under the three conditions of `jn_iff` (the third is the value's own field hf):
    what is claimed before the first round is `Idn m ∧ Keys x m ∧ J11 x m`: the later groups' two
    sentences (ValueSays.lean) and (J11).

Limits. K04_law IS NOT PROVED BY THIS. THE TOKENS IN (J11) ARE THE VALUE's LETTER tok AT THE FIRST
STATEMENT x: NOTHING HERE TIES THEM TO THE TOKENS THAT K4's HEARING READS (the seat's tokv), NOR TO
A REQUEST. (J11) RUNS OVER ALL 2 ^ lT POSITIONS, whatever the request's length. At a position whose
token is not below the vocabulary's size the library's embR is 0 (the head of OwnFirstW.lean): there
(J11) says that the stream's entries are 0. Those of ValueSays.lean: that KF is the extension of a
call's key vector is not shown here; that zOf, kTg, kIncS are what a program's lookup left is not
said; the identity that the selector's entries sum to 1 is no part of `Idn`.
-/
import Johnson.Road.K4.ValueSays
import Johnson.Road.K4.CarriageFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Finset
open Inst.Model (Scl)
open Inst.Model.FFSeg (xS embR)

noncomputable section

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type}

namespace Plan4F
variable (Q : Plan4F E M X)

/-- (J11) at every feature and every position, at the tokens that the value's letter tok reads off
the first statement. -/
def J11 (x : X) (m : M) : Prop :=
  ∀ F < Q.D.d, ∀ p < 2 ^ Q.D.lT,
    xS Q.D (Q.toPlan4.cells m) 0 F p =
      embR Q.D.P Q.kW (Q.Wn (Q.toPlan4.msg m)) (Q.tok x p) F

/-- **What is claimed before the first chain's first round, in the value's own letters**, under the
two public conditions C and hk of the library's join. -/
theorem pTF_iff (C : Q.D.ChOK)
    (hk : ∀ l, l < Q.D.nl →
      (Q.D.Pl l).kq = (Q.D.Pl l).kk ∨ (16 ≤ (Q.D.Pl l).kq ∧ 16 ≤ (Q.D.Pl l).kk))
    (x : X) (m : M) :
    Q.fullF.ownF.pT x m ↔ Q.toPlan4.Idn m ∧ Q.toPlan4.Keys x m ∧ Q.J11 x m := by
  have hj : Q.toPlan4.full.jg x (Q.toPlan4.full.tS x m) m = 0 ↔ Q.toPlan4.Keys x m := by
    rw [Q.toPlan4.full.jn_iff C hk Q.hf x m, Q.toPlan4.kEnd_eq x m]
    exact Iff.rfl
  have hg : (∀ V < 2 ^ Q.gB, ∀ U < 2 ^ (Q.ls + Q.D.lT),
      embGap Q.nb Q.ls Q.D.lT (Q.fullF.ofp.fs.fE x m) U V = 0) ↔ Q.J11 x m := by
    rw [emb_zero Q.nb Q.ls Q.D.lT Q.gB Q.hnb]
    constructor
    · intro h F hF p hp
      have h2 : 0 < 2 ^ Q.ls := Nat.two_pow_pos _
      have h1 : F / 2 ^ Q.ls < Q.nb := by
        rw [Q.hd] at hF
        exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hF)
      have e := sub_eq_zero.1 (h (F / 2 ^ Q.ls) h1 (F % 2 ^ Q.ls) (Nat.mod_lt _ h2) p hp)
      rw [Nat.div_add_mod'] at e
      exact e
    · intro h kh hkh r hr p hp
      have hF : kh * 2 ^ Q.ls + r < Q.D.d := by
        rw [Q.hd]
        calc kh * 2 ^ Q.ls + r < kh * 2 ^ Q.ls + 2 ^ Q.ls := Nat.add_lt_add_left hr _
          _ = (kh + 1) * 2 ^ Q.ls := by ring
          _ ≤ Q.nb * 2 ^ Q.ls := Nat.mul_le_mul_right _ hkh
      exact sub_eq_zero.2 (h _ hF p hp)
  exact (Q.fullF.ownF_pT x m).trans
    ⟨fun h => ⟨h.1, hj.1 h.2.1, hg.1 h.2.2⟩, fun h => ⟨h.1, hj.2 h.2.1, hg.2 h.2.2⟩⟩

end Plan4F
end
end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4F.pTF_iff
