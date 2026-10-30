-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/At/First.lean: what the first layers' sub-proof's own rounds have beside the others
(LayVOF, Cb/Pv/Lay/OwnAll.lean; Emb.lean, EmbSide.lean), at a value: the library's identity (J11):
each entry of the stream that comes in is the entry of the embedding's row of that position's token.

Main names:
  `FirstPar`: over the letters of Cb/Pv/Lay/At/Fore.lean: the bits ls of a feature's low part, the
    number nb of high parts (d = nb 2^ls), the coordinates gB of the second further point; the
    embedding as read off the entries (emb); the request's tokens in the first statement (tok).
  `fE`: the defect of (J11) at a feature and a position. `eG`: the gaps of Emb.lean: embGap of fE.
  `sumX`, `sumE`: the stream's and the embedding's side at two points, in the form of emb_side
    (Cb/Pv/Lay/EmbSide.lean).
  `Rd0F`: what is carried from the start to the weights' claims: the gaps' extension over both
    indices vanishes at the two points. `QF`, `Q0F`: what is carried along behind and before the
    token point. `x0F`, `pvF`: the first statement and the token point inside a statement behind
    the three points.
  `rd0_iff`: Rd0F says that the two sides are equal.
  `first_atPt`, `first_atTwo`: the two fields atPt and atTwo of LayVOF at these letters.
  `q0_j11`, `q0_j11_all`: Q0F gives (J11) at every feature below d and every position.

Limits: that the programs' two claims on the embedding are these sides is not said here. Nothing is
said on an honest prover or on hiding.


-/
import Cb.Pv.Lay.At.Fore
import Cb.Pv.Lay.EmbSide

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.At
open Iop Prob Cb IOR Finset TWhole
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell LW dJ xS)

noncomputable section

/-- The letters of the first sub-proof that stay free, beside those of At/Fore.lean. -/
structure FirstPar (E : Type) [Field E] [Fintype E] [scl : Scl] (M X : Type)
    extends ForePar E M X where
  /-- the bits of a feature's low part; the number of high parts; the second point's coordinates -/
  ls : ℕ
  nb : ℕ
  gB : ℕ
  hnb : nb ≤ 2 ^ gB
  /-- the features are the pairs of a high and a low part -/
  hd : D.d = nb * 2 ^ ls
  /-- the embedding, read off the entries: by token and feature; the request's tokens -/
  emb : (J → E) → ℕ → ℕ → E
  tok : X → ℕ → ℕ

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type}

namespace FirstPar
variable (P : FirstPar E M X)

/-- The statements behind the token point; behind the three points. -/
abbrev XT : Type := X × (Fin P.D.lT → E)
abbrev X3 : Type := (P.XT × (Fin (P.ls + P.D.lT) → E)) × (Fin P.gB → E)

/-- The first statement and the token point inside a statement behind the three points. -/
def x0F (z : P.X3) : X := z.1.1.1
def pvF (z : P.X3) : Fin P.D.lT → E := z.1.1.2

/-- The defect of (J11) at a feature and a position. -/
def fE (x : X) (m : M) (F i : ℕ) : E :=
  xS P.D (P.rd (P.msg m)) 0 F i - P.emb (P.msg m) (P.tok x i) F

/-- The gaps. -/
def eG (y : P.XT) (m : M) (U V : ℕ) : E := embGap P.nb P.ls P.D.lT (P.fE y.1 m) U V

/-- A function of a feature and a position, summed under the three equality weights. -/
def side (f : ℕ → ℕ → E) (pa pb : ℕ → E) : E :=
  ∑ kh ∈ range P.nb, Blocks.eqN P.gB 0 pb kh *
    ∑ r ∈ range (2 ^ P.ls), Blocks.eqN P.ls 0 pa r *
      ∑ p ∈ range (2 ^ P.D.lT), Blocks.eqN P.D.lT P.ls pa p * f (kh * 2 ^ P.ls + r) p

/-- The stream's side; the embedding's side. -/
def sumX (m : M) (pa pb : ℕ → E) : E := P.side (fun F i => xS P.D (P.rd (P.msg m)) 0 F i) pa pb
def sumE (x : X) (m : M) (pa pb : ℕ → E) : E :=
  P.side (fun F i => P.emb (P.msg m) (P.tok x i) F) pa pb

/-- What is carried from the start to the weights' claims. -/
def Rd0F (z : P.X3) (m : M) : Prop :=
  Blocks.ext P.gB (fun V => Blocks.ext (P.ls + P.D.lT) (fun U => P.eG z.1.1 m U V)
    (Blocks.nat z.1.2)) (Blocks.nat z.2) = 0

theorem side_sub (f g : ℕ → ℕ → E) (pa pb : ℕ → E) :
    P.side (fun F i => f F i - g F i) pa pb = P.side f pa pb - P.side g pa pb := by
  unfold side
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun kh _ => ?_
  rw [← mul_sub, ← sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun r _ => ?_
  rw [← mul_sub, ← sum_sub_distrib]
  congr 1
  exact sum_congr rfl fun p _ => by ring

/-- **What is carried says that the two sides are equal.** -/
theorem rd0_iff (z : P.X3) (m : M) :
    P.Rd0F z m ↔
      P.sumE (P.x0F z) m (Blocks.nat z.1.2) (Blocks.nat z.2) =
        P.sumX m (Blocks.nat z.1.2) (Blocks.nat z.2) := by
  unfold Rd0F eG
  rw [emb_side P.nb P.ls P.D.lT P.gB P.hnb]
  have e := P.side_sub (fun F i => xS P.D (P.rd (P.msg m)) 0 F i)
    (fun F i => P.emb (P.msg m) (P.tok z.1.1.1 i) F) (Blocks.nat z.1.2) (Blocks.nat z.2)
  have e' : (∑ kh ∈ range P.nb, Blocks.eqN P.gB 0 (Blocks.nat z.2) kh *
      ∑ r ∈ range (2 ^ P.ls), Blocks.eqN P.ls 0 (Blocks.nat z.1.2) r *
        ∑ p ∈ range (2 ^ P.D.lT), Blocks.eqN P.D.lT P.ls (Blocks.nat z.1.2) p *
          P.fE z.1.1.1 m (kh * 2 ^ P.ls + r) p) =
      P.sumX m (Blocks.nat z.1.2) (Blocks.nat z.2) -
        P.sumE (P.x0F z) m (Blocks.nat z.1.2) (Blocks.nat z.2) := e
  rw [e', sub_eq_zero]
  exact eq_comm

/-- What is carried along behind the token point: the defects' extensions vanish at it, and the join
at the true sum of the terms. -/
def QF (y : P.XT) (m : M) : Prop :=
  (∀ k : ℕ × Fin P.D.nNu,
    Blocks.ext P.D.lT (dJ P.D (P.rd (P.msg m)) k.1 k.2) (Blocks.nat y.2) = 0) ∧
    P.jg y.1 (P.tS y.1 m) m = 0

/-- What is carried along before the token point: the join, and all gaps of (J11). -/
def Q0F (x : X) (m : M) : Prop :=
  P.jg x (P.tS x m) m = 0 ∧
    ∀ V < 2 ^ P.gB, ∀ U < 2 ^ (P.ls + P.D.lT), embGap P.nb P.ls P.D.lT (P.fE x m) U V = 0

/-- **The field atPt of LayVOF.** -/
theorem first_atPt (x : X) (p : Fin P.D.lT → E) (m : M)
    (h : (∀ V < 2 ^ P.gB, ∀ U < 2 ^ (P.ls + P.D.lT), P.eG (x, p) m U V = 0) ∧ P.QF (x, p) m) :
    (∀ k : ℕ × Fin P.D.nNu,
      Blocks.ext P.D.lT (dJ P.D (P.rd (P.msg m)) k.1 k.2) (Blocks.nat p) = 0) ∧ P.Q0F x m :=
  ⟨h.2.1, h.2.2, h.1⟩

/-- **The field atTwo of LayVOF.** -/
theorem first_atTwo (z : P.X3) (m : M)
    (h : (P.toForePar.fore P.x0F P.pvF P.Rd0F).H.pL z m) :
    Blocks.ext P.gB (fun V => Blocks.ext (P.ls + P.D.lT) (fun U => P.eG z.1.1 m U V)
      (Blocks.nat z.1.2)) (Blocks.nat z.2) = 0 ∧ P.QF z.1.1 m := by
  obtain ⟨h1, h2, h3⟩ := P.toForePar.fore_atPt P.x0F P.pvF P.Rd0F z m h
  exact ⟨h3, h1, h2⟩

/-- What is claimed before the first round gives (J11). -/
theorem q0_j11 (x : X) (m : M) (h : P.Q0F x m) :
    ∀ kh < P.nb, ∀ r < 2 ^ P.ls, ∀ p < 2 ^ P.D.lT,
      xS P.D (P.rd (P.msg m)) 0 (kh * 2 ^ P.ls + r) p =
        P.emb (P.msg m) (P.tok x p) (kh * 2 ^ P.ls + r) := fun kh hkh r hr p hp =>
  sub_eq_zero.1 ((emb_zero P.nb P.ls P.D.lT P.gB P.hnb (P.fE x m)).1 h.2 kh hkh r hr p hp)

/-- **What is claimed before the first round gives (J11) at every feature and every position.** -/
theorem q0_j11_all (x : X) (m : M) (h : P.Q0F x m) (F : ℕ) (hF : F < P.D.d) (p : ℕ)
    (hp : p < 2 ^ P.D.lT) :
    xS P.D (P.rd (P.msg m)) 0 F p = P.emb (P.msg m) (P.tok x p) F := by
  have h2 : 0 < 2 ^ P.ls := Nat.two_pow_pos _
  have h1 : F / 2 ^ P.ls < P.nb := by
    rw [P.hd] at hF
    exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hF)
  have e := P.q0_j11 x m h (F / 2 ^ P.ls) h1 (F % 2 ^ P.ls) (Nat.mod_lt _ h2) p hp
  rwa [Nat.div_add_mod'] at e

end FirstPar
end
end Cb.Pv.Lay.At

#print axioms Cb.Pv.Lay.At.FirstPar.rd0_iff
#print axioms Cb.Pv.Lay.At.FirstPar.first_atPt
#print axioms Cb.Pv.Lay.At.FirstPar.first_atTwo
#print axioms Cb.Pv.Lay.At.FirstPar.q0_j11
#print axioms Cb.Pv.Lay.At.FirstPar.q0_j11_all
