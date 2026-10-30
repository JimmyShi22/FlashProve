-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/StageBoth.lean: one challenge in two roles: a stage with a second pair of relations. (Words
of this library: lean/GLOSSARY.md.)

A stage keeps its protocol and gets a second pair of relations. The second pair that is needed most
is a second zero test, called a rider: a polynomial that is not zero remains non-zero at a point
whose coordinates are challenges of chosen rounds of the stage, with prover messages in between.

No further message and no further check. A rider concerns the analysis only: the verifier sends
nothing more and checks nothing more; some of its challenges have more bad values.
Why the errors are maxima. A statement outside "R and R'" is outside R or outside R'. In the first
case the prover is doomed by the first soundness statement, in the second case by the second. So the
error of a round is the larger of the two errors, not their sum (`Block.Clean.both`). The bound is
smaller than the sum, because the set of bad values may depend on which of the two relations fails:
max (2, 1) = 2 for a round challenge of a product layer and max (1, 1) = 1 for its ζ.
A consequence: a second test of degree 1 in each variable changes no error of a sumcheck, or of a
product layer whose error at ζ is at least 1 (`Stage.both_eq_self`, `SC.err_binds_le`, h0 of
`PL.err_binds_le`; for a layer of the lookup argument's product tree over the looked-up values:
`Lk.stK_both_one`, Blocks/LookupRider.lean).
Limits. (a) A round binds at most one variable, and the map that computes the field element from the
verifier message is injective: so a verifier message that is a point (several coordinates in one
message) cannot be used for a rider. (b) A rider ends in one equation, G is 0 at the point:
variables of G that a later stage would bind are not covered. Neither is needed for the coordinates
of the end point z of the lookup argument (Blocks/LookupStage.lean), which are single challenges of
one layer.

 1. `Binds κ E s`: for each round of s: nothing, or a variable k : κ that the challenge of this
    round binds. `Binds.pt`, `vars`, `err d`, `app`.
 2. `Vanishes G z T`: G is 0 at every point that agrees with z outside the variables in T.
 3. `Block.clean_rider`: `doomed_rider` as a soundness statement for any block, whatever else its
    rounds do.
 4. `Stage.both`: the stage with the same protocol and the larger errors; `Stage.Props.both`,
    `both'`: `Stage.Props` for both pairs of relations; the honest prover, `Hon.Masked` and the
    withheld set `Hon.withheld` (Blocks/BlockHon.lean) are unchanged. `Stage.Props.rider`: item 3
    for a stage; `rider_all`: when all variables of G are bound. `selOf`.
 5. The masked sumcheck: `SC.binds`, `SC.pt_binds`. The product layer: `PL.binds`, `PL.pt_binds`,
    `PL.mem_vars_binds`. Each bound coordinate of the rider's point is a coordinate of the end
    point, or of the next point (ζ | ϱ̂). The hypotheses are listed at these theorems.
 6. Multilinear extensions of arrays: `vanishes_ext`, `degLE_ext_comp`.
 7. `Stage.Below.both`, `Stage.both_eq_self`; rounds, pads, probabilities and tracking data are
    those of the stage, by rfl.

Round-by-round soundness is the notion of R. Canetti, Y. Chen, J. Holmgren, A. Lombardi, G.
Rothblum, R. Rothblum, ePrint 2018/1004, Definition 5.3.
-/
import Blocks.StageLib
import Blocks.SumCheckStage
import Blocks.StageNums
import Prob.Bias
import Blocks.LookupRel
import Blocks.ProductBlock
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Blocks
open Iop Prob Alg
open scoped ENNReal

/-! ## 1. Which round binds which variable -/

/-- For each round of a list of rounds: nothing, or a variable, with the map that computes an
element of E from the verifier message of the round. -/
def Binds (κ E : Type) : Shape → Type
  | [] => Unit
  | r :: s => Option (κ × (r.Chal → E)) × Binds κ E s

namespace Binds

variable {κ E : Type}

/-- two lists of rounds in a row -/
def app : {s t : Shape} → Binds κ E s → Binds κ E t → Binds κ E (s ++ t)
  | [], _, _, b => b
  | _ :: _, _, (o, a), b => (o, app a b)

/-- the variables that are bound, in the order of the rounds -/
def vars : {s : Shape} → Binds κ E s → List κ
  | [], _ => []
  | _ :: _, (Option.none, b) => vars b
  | _ :: _, (some (k, _), b) => k :: vars b

/-- the errors: d k bad values in a round that binds k -/
def err (d : κ → ℕ) : {s : Shape} → Binds κ E s → Err s
  | [], _ => ()
  | _ :: _, (Option.none, b) => (0, err d b)
  | _ :: _, (some (k, _), b) => (d k, err d b)

/-- different verifier messages give different elements -/
def Inj : {s : Shape} → Binds κ E s → Prop
  | [], _ => True
  | _ :: _, (Option.none, b) => Inj b
  | _ :: _, (some (_, f), b) => Function.Injective f ∧ Inj b

variable [DecidableEq κ]

/-- The point after all rounds: z, with the challenge at each variable that a round binds. -/
def pt : {s : Shape} → Binds κ E s → Rho s → (κ → E) → κ → E
  | [], _, _, z => z
  | _ :: _, (Option.none, b), (_, ρ), z => pt b ρ z
  | _ :: _, (some (k, f), b), (c, ρ), z => pt b ρ (Function.update z k (f c))

/-- Outside the bound variables the point is z. -/
theorem pt_of_notMem :
    ∀ {s : Shape} (b : Binds κ E s) (ρ : Rho s) (z : κ → E) {j : κ}, j ∉ b.vars → b.pt ρ z j = z j
  | [], _, _, _, _, _ => rfl
  | _ :: _, (Option.none, b), (_, ρ), z, _, hj => pt_of_notMem b ρ z hj
  | _ :: _, (some (k, f), b), (c, ρ), z, j, hj => by
      have h1 : j ∉ vars b := fun h => hj (List.mem_cons_of_mem _ h)
      have h2 : j ≠ k := fun h => hj (h ▸ List.mem_cons_self)
      show pt b ρ (Function.update z k (f c)) j = z j
      rw [pt_of_notMem b ρ _ h1, Function.update_of_ne h2]



omit [DecidableEq κ] in
theorem vars_app :
    ∀ {s t : Shape} (a : Binds κ E s) (b : Binds κ E t), (app a b).vars = a.vars ++ b.vars
  | [], _, _, _ => rfl
  | _ :: _, _, (Option.none, a), b => vars_app a b
  | _ :: _, _, (some (k, _), a), b => congrArg (k :: ·) (vars_app a b)

omit [DecidableEq κ] in
theorem err_app (d : κ → ℕ) :
    ∀ {s t : Shape} (a : Binds κ E s) (b : Binds κ E t),
      (app a b).err d = Err.app (a.err d) (b.err d)
  | [], _, _, _ => rfl
  | _ :: _, _, (Option.none, a), b => Prod.ext rfl (err_app d a b)
  | _ :: _, _, (some _, a), b => Prod.ext rfl (err_app d a b)

omit [DecidableEq κ] in
theorem Inj.app :
    ∀ {s t : Shape} {a : Binds κ E s} {b : Binds κ E t}, a.Inj → b.Inj → (Binds.app a b).Inj
  | [], _, _, _, _, hb => hb
  | _ :: s, _, (Option.none, a), b, ha, hb => Inj.app (s := s) (a := a) (b := b) ha hb
  | _ :: s, _, (some _, a), b, ha, hb => ⟨ha.1, Inj.app (s := s) (a := a) (b := b) ha.2 hb⟩

theorem pt_app : ∀ {s t : Shape} (a : Binds κ E s) (b : Binds κ E t) (ρ : Rho (s ++ t)) (z : κ → E),
    (app a b).pt ρ z = b.pt (Rho.snd (s := s) ρ) (a.pt (Rho.fst ρ) z)
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, (Option.none, a), b, (_, ρ), z => pt_app a b ρ z
  | _ :: _, _, (some (k, f), a), b, (c, ρ), z => pt_app a b ρ (Function.update z k (f c))

end Binds

/-! ## 2. A polynomial that does not vanish: the bad values of the challenges -/

section Rider

variable {κ E : Type}

/-- G vanishes in the variables of T: it is 0 at every point that agrees with z outside T. -/
def Vanishes [Zero E] (G : (κ → E) → E) (z : κ → E) (T : List κ) : Prop :=
  ∀ z' : κ → E, (∀ j, j ∉ T → z' j = z j) → G z' = 0

theorem vanishes_nil [Zero E] (G : (κ → E) → E) (z : κ → E) : Vanishes G z [] ↔ G z = 0 :=
  ⟨fun h => h z fun _ _ => rfl,
    fun h z' hz => by rw [funext fun j => hz j List.not_mem_nil]; exact h⟩

variable [Field E] [Fintype E] [DecidableEq κ]

/-- One variable, under hG, h: for all but at most d k values of the challenge at k, G does not
vanish in T. -/
theorem cnt_vanishes_le {d : κ → ℕ} {G : (κ → E) → E} (hG : DegLE d G) {z : κ → E} {k : κ}
    {T : List κ} (h : ¬ Vanishes G z (k :: T)) :
    cnt (fun r : E => Vanishes G (Function.update z k r) T) ≤ d k := by
  unfold Vanishes at h
  push Not at h
  obtain ⟨z', hz', hne⟩ := h
  obtain ⟨q, hq, he⟩ := hG z' k
  have hq0 : q ≠ 0 := fun h0 => hne (by
    have := he (z' k)
    rw [Function.update_eq_self, h0, Polynomial.eval_zero] at this
    exact this)
  refine (cnt_mono fun r hr => ?_).trans (count_roots_le hq0 hq)
  rw [← he r]
  refine hr _ fun j hj => ?_
  by_cases hjk : j = k
  · subst hjk
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hjk, Function.update_of_ne hjk]
    exact hz' j fun hm => (List.mem_cons.1 hm).elim hjk hj

/-- The rider, on chosen rounds of any list of rounds (with `Binds.Inj`). If G has degree at most d
k in each variable k and does not vanish in the variables that the chosen rounds bind, then the
prover is doomed with respect to "G is not 0 at the point": whatever it sends in between, at most d
k values of the challenge that binds k are bad, and no value of another challenge. -/
theorem doomed_rider {d : κ → ℕ} {G : (κ → E) → E} (hG : DegLE d G) :
    ∀ {s : Shape} (b : Binds κ E s), b.Inj →
      ∀ z : κ → E, ¬ Vanishes G z b.vars → Doomed s (b.err d) (fun τ => G (b.pt τ.rho z) ≠ 0)
  | [], _, _, z, h => fun h0 => h ((vanishes_nil G z).2 h0)
  | _ :: _, (Option.none, b), hb, z, h => fun m => by
      refine le_of_eq (cnt_false fun c hc => hc ?_)
      exact doomed_rider hG b hb z h
  | r :: _, (some (k, f), b), hb, z, h => fun m => by
      have h1 : ∀ c : r.Chal,
          ¬ Doomed _ (b.err d) (fun τ => G (b.pt τ.rho (Function.update z k (f c))) ≠ 0) →
          Vanishes G (Function.update z k (f c)) b.vars :=
        fun c hc => by_contra fun hv => hc (doomed_rider hG b hb.2 _ hv)
      refine (cnt_mono h1).trans ?_
      refine (cnt_comp_le f (w := 1)
        (fun e => cnt_le_one fun a a' ha ha' => hb.1 (ha.trans ha'.symm))
        fun r => Vanishes G (Function.update z k r) b.vars).trans ?_
      rw [Nat.mul_one]
      exact cnt_vanishes_le hG h

end Rider

/-! ## 3. The rider on a block -/

section Block

variable {κ E Xi Yi Xo Yo : Type} [Field E] [Fintype E] [DecidableEq κ]

/-- The rider as a soundness statement, for any block B and any choice b of rounds with `Binds.Inj`.
G x y, of degree at most d, is the polynomial of the second test: it is fixed by the input
statement. z₀ holds the coordinates that are fixed already. hout: the output relation implies that G
is 0 at the point. -/
theorem Block.clean_rider (B : Block Xi Yi Xo Yo) (b : Binds κ E B.shape) (hb : b.Inj)
    {d : κ → ℕ} {G : Xi → Yi → (κ → E) → E} (hG : ∀ x y, DegLE d (G x y))
    (z₀ : Xi → Yi → κ → E) {Ro : Xo → Yo → Prop}
    (hout : ∀ x y τ xo,
      B.pub x τ.rho τ.plains = some xo → Ro xo (B.imp y τ) → G x y (b.pt τ.rho (z₀ x y)) = 0) :
    B.Clean (fun x y => Vanishes (G x y) (z₀ x y) b.vars) Ro (b.err d) :=
  Block.clean_iff.2 fun x y hxy =>
    Doomed.mono _ _ (fun τ hτ xo hxo hRo => hτ (hout x y τ xo hxo hRo))
      (doomed_rider (hG x y) b hb (z₀ x y) hxy)

end Block

/-! ## 4. Stages -/

section Stage

variable {P E : Type} [Fintype P] [DecidableEq P] [AddCommGroup E] [Fintype E] {a b : Sorts}

omit [Fintype P] [DecidableEq P] [AddCommGroup E] [Fintype E] in
/-- The same protocol with a second list of errors: in each round the larger of the two. -/
def Stage.both (S : Stage P E a b) (ε' : Err S.B.shape) : Stage P E a b :=
  { S with ε := Err.max S.ε ε' }

omit [Fintype P] [DecidableEq P] [AddCommGroup E] [Fintype E] in
theorem Stage.toCore_both (S : Stage P E a b) (ε' : Err S.B.shape) :
    (S.both ε').toCore = S.toCore := rfl

variable {S : Stage P E a b} {ca : Cut P E a} {cb : Cut P E b} {ε' : Err S.B.shape}
  {K : a.X → a.Y → Prop} {K' : b.X → b.Y → Prop} {KH : a.I → (P → E) → a.X → a.Y → Prop}
  {KH' : b.I → (P → E) → b.X → b.Y → Prop}

/-- One stage, two pairs of relations. The second pair needs its own soundness statement, with its
own errors. For the honest run: the second condition before the stage implies the one after it; the
stage's own relations for the honest run may be assumed, and that the outputs are the stage's own.
Masked form, the withheld set and the bounds for the probabilities of its two parts are those of the
stage. -/
theorem Stage.Props.both' (h : S.Props ca cb) (hc : S.B.Clean K K' ε')
    (hKH : ∀ s π x y ρ xo, ρ ∉ S.H.withheld s → S.B.pub x ρ (S.H.tr s π ρ).plains = some xo →
      ca.Hn s π x y → cb.Hn (S.H.next s ρ) π xo (S.B.imp y (S.H.tr s π ρ)) → KH s π x y →
      KH' (S.H.next s ρ) π xo (S.B.imp y (S.H.tr s π ρ))) :
    (S.both ε').Props (ca.and K KH) (cb.and K' KH') where
  clean := h.clean.both hc
  acc := h.acc.frame hKH
  masked := h.masked
  keeps := h.keeps
  prBad := h.prBad
  prWin := h.prWin

/-- `Stage.Props.both'`, from a completeness statement (`Hon.AccOn`) for the second pair. -/
theorem Stage.Props.both (h : S.Props ca cb) (hc : S.B.Clean K K' ε') (ha : S.H.AccOn KH KH') :
    (S.both ε').Props (ca.and K KH) (cb.and K' KH') where
  clean := h.clean.both hc
  acc := h.acc.and ha
  masked := h.masked
  keeps := h.keeps
  prBad := h.prBad
  prWin := h.prWin

end Stage

section StageRider

variable {P E κ : Type} [Fintype P] [DecidableEq P] [Field E] [Fintype E]
  [DecidableEq κ] {a b : Sorts}

/-- The rider on a stage S with `Stage.Props`. The chosen rounds of S (with `Binds.Inj`) are used
for a second zero test. G x y, of degree at most d k in the variable k, is fixed by the statement
before the stage; K' is the condition on it after the stage. hiff: K' holds if and only if G is 0 at
the point whose coordinates are the chosen challenges, and those of z₀ elsewhere. Then the condition
before the stage is: G vanishes in the bound variables. Protocol, honest prover and masked form are
those of S; a chosen round has the error max (its own) (d k). -/
theorem Stage.Props.rider {S : Stage P E a b} {ca : Cut P E a} {cb : Cut P E b} (h : S.Props ca cb)
    (bd : Binds κ E S.B.shape) (hb : bd.Inj) {d : κ → ℕ} {G : a.X → a.Y → (κ → E) → E}
    (hG : ∀ x y, DegLE d (G x y)) (z₀ : a.X → a.Y → κ → E) {K' : b.X → b.Y → Prop}
    (hiff : ∀ x y τ xo, S.B.pub x τ.rho τ.plains = some xo →
      (K' xo (S.B.imp y τ) ↔ G x y (bd.pt τ.rho (z₀ x y)) = 0)) :
    (S.both (bd.err d)).Props
      (ca.and (fun x y => Vanishes (G x y) (z₀ x y) bd.vars) fun _ _ x y =>
        Vanishes (G x y) (z₀ x y) bd.vars)
      (cb.and K' fun _ _ x y => K' x y) :=
  h.both' (S.B.clean_rider bd hb hG z₀ fun x y τ xo hxo hK => (hiff x y τ xo hxo).1 hK)
      fun s π x y ρ xo _ hxo _ _ hv => by
    have e : (S.H.tr s π ρ).rho = ρ := S.H.rho_tr s π ρ
    refine (hiff x y (S.H.tr s π ρ) xo (by rw [e]; exact hxo)).2 (hv _ fun j hj => ?_)
    exact bd.pt_of_notMem _ _ hj

/-- `Stage.Props.rider` when the chosen rounds bind all variables of G: the condition before the
stage is that G is the zero function. -/
theorem Stage.Props.rider_all {S : Stage P E a b} {ca : Cut P E a} {cb : Cut P E b}
    (h : S.Props ca cb) (bd : Binds κ E S.B.shape) (hb : bd.Inj) (hall : ∀ k, k ∈ bd.vars)
    {d : κ → ℕ} {G : a.X → a.Y → (κ → E) → E} (hG : ∀ x y, DegLE d (G x y)) {K' : b.X → b.Y → Prop}
    (hiff : ∀ x y τ xo, S.B.pub x τ.rho τ.plains = some xo →
      (K' xo (S.B.imp y τ) ↔ G x y (bd.pt τ.rho fun _ => 0) = 0)) :
    (S.both (bd.err d)).Props (ca.and (fun x y => ∀ z, G x y z = 0) fun _ _ x y => ∀ z, G x y z = 0)
      (cb.and K' fun _ _ x y => K' x y) :=
  (h.rider bd hb hG (fun _ _ _ => 0) hiff).conseq
    (fun _ _ hR => ⟨hR.1, fun z => hR.2 z fun j hj => absurd (hall j) hj⟩)
    (fun _ _ hR => hR) (fun _ _ _ _ hH => ⟨hH.1, fun z _ => hH.2 z⟩) (fun _ _ _ _ hH => hH)
    (fun _ hV => hV) fun _ hV => hV

end StageRider

/-! ### From the coordinate used for a variable to the variable that a coordinate is used for -/

section SelOf

variable {n : ℕ}

/-- The variable that the coordinate t is used for, if σ k is the coordinate used for the variable
k. -/
def selOf (σ : Fin n → ℕ) (t : ℕ) : Option (Fin n) := (List.finRange n).find? fun k => σ k = t

theorem selOf_eq_some {σ : Fin n → ℕ} {t : ℕ} {k : Fin n} (h : selOf σ t = some k) : σ k = t := by
  have := List.find?_some h
  simpa using this

theorem selOf_apply {σ : Fin n → ℕ} (hσ : Function.Injective σ) (k : Fin n) :
    selOf σ (σ k) = some k := by
  cases h : selOf σ (σ k) with
  | none =>
    have := List.find?_eq_none.1 h k (List.mem_finRange k)
    simp at this
  | some k' => rw [hσ (selOf_eq_some h)]

/-- Different coordinates are used for different variables. -/
theorem selOf_inj {σ : Fin n → ℕ} {t t' : ℕ} {k : Fin n}
    (h : selOf σ t = some k) (h' : selOf σ t' = some k) : t = t' :=
  (selOf_eq_some h).symm.trans (selOf_eq_some h')

end SelOf

/-! ## 5. The masked sumcheck -/

namespace SC

variable {E Y P Ξ ι κ : Type}
  [Field E] [Fintype E] [DecidableEq E] [DecidableEq ι] (S : SC E Y P Ξ ι)

/-- The rounds of a masked sumcheck as rounds of a rider: the round that binds the variable i of
the sumcheck binds the variable sel i of the rider, if there is one. -/
def binds (sel : ι → Option κ) : (l : List ι) → Binds κ E (S.sc l).shape
  | [] => ()
  | i :: l => ((sel i).map fun k => (k, fun c : E => c), binds sel l)

theorem vars_binds (sel : ι → Option κ) : ∀ l : List ι, (S.binds sel l).vars = l.filterMap sel
  | [] => rfl
  | i :: l => by
      have ih := vars_binds sel l
      cases h : sel i with
      | none =>
        rw [List.filterMap_cons_none h, ← ih]
        show Binds.vars (s := S.rd i :: (S.sc l).shape)
            ((sel i).map fun k => (k, fun c : E => c), S.binds sel l) = _
        rw [h]
        rfl
      | some k =>
        rw [List.filterMap_cons_some h, ← ih]
        show Binds.vars (s := S.rd i :: (S.sc l).shape)
            ((sel i).map fun k => (k, fun c : E => c), S.binds sel l) = _
        rw [h]
        rfl

theorem inj_binds (sel : ι → Option κ) : ∀ l : List ι, (S.binds sel l).Inj
  | [] => trivial
  | i :: l => by
      show Binds.Inj (s := S.rd i :: (S.sc l).shape)
        ((sel i).map fun k => (k, fun c : E => c), S.binds sel l)
      cases sel i with
      | none => exact inj_binds sel l
      | some k => exact ⟨fun _ _ h => h, inj_binds sel l⟩

omit [Fintype E] in
/-- One round stores its challenge at its variable. -/
theorem point_of_pb {i : ι} {x xo : S.X} {r : E}
    {m : Fin (S.e i + 1) → E} (h : S.pb i x r m = some xo) :
    xo.2.1 = Function.update x.2.1 i r := by
  unfold pb at h
  by_cases hr : S.nzv i = true ∧ r = 0
  · rw [if_pos hr] at h
    exact absurd h (by simp)
  · rw [if_neg hr] at h
    rw [← Option.some.inj h]

/-- The coordinates of the variables that the sumcheck does not bind are unchanged in its output. -/
theorem point_of_pub_sc :
    ∀ (l : List ι) (x xo : S.X) (ρ : Rho (S.sc l).shape) (p : Plains (S.sc l).shape),
      (S.sc l).pub x ρ p = some xo → ∀ j, j ∉ l → xo.2.1 j = x.2.1 j
  | [], x, xo, _, _, h, _, _ => by rw [← Option.some.inj h]
  | i :: l, x, xo, ρ, p, h, j, hj => by
      obtain ⟨x', hx', hxo⟩ := Option.bind_eq_some_iff.mp h
      have hji : j ≠ i := fun e => hj (by rw [e]; exact List.mem_cons_self)
      have hx'' : S.pb i x ρ.1 p.1 = some x' := hx'
      rw [point_of_pub_sc l x' xo _ _ hxo j fun hm => hj (List.mem_cons_of_mem _ hm),
        S.point_of_pb hx'', Function.update_of_ne hji]

variable [DecidableEq κ]

/-- Where the verifier of the sumcheck does not reject: for i in the list with sel i = some k, the
coordinate k of the point of the rider is the coordinate i of the end point of the sumcheck, if the
list has no variable twice and different variables of the list have different images. -/
theorem pt_binds (sel : ι → Option κ) :
    ∀ (l : List ι), l.Nodup → (∀ i ∈ l, ∀ i' ∈ l, ∀ k, sel i = some k → sel i' = some k → i = i') →
      ∀ (x xo : S.X) (ρ : Rho (S.sc l).shape) (p : Plains (S.sc l).shape) (z : κ → E),
        (S.sc l).pub x ρ p = some xo →
        ∀ i ∈ l, ∀ k, sel i = some k → (S.binds sel l).pt ρ z k = xo.2.1 i
  | [], _, _, _, _, _, _, _, _, i, hi, _, _ => absurd hi List.not_mem_nil
  | i₀ :: l, hl, hs, x, xo, ρ, p, z, h, i, hi, k, hk => by
      obtain ⟨x', hx', hxo⟩ := Option.bind_eq_some_iff.mp h
      have hl' := (List.nodup_cons.1 hl)
      have hs' : ∀ i ∈ l, ∀ i' ∈ l, ∀ k, sel i = some k → sel i' = some k → i = i' :=
        fun a ha a' ha' k' => hs a (List.mem_cons_of_mem _ ha) a' (List.mem_cons_of_mem _ ha') k'
      have hx'' : S.pb i₀ x ρ.1 p.1 = some x' := hx'
      rcases List.mem_cons.1 hi with rfl | hi'
      · -- the variable of the first round
        have hnot : k ∉ (S.binds sel l).vars := by
          rw [S.vars_binds, List.mem_filterMap]
          rintro ⟨i', hi', hk'⟩
          exact hl'.1 ((hs i List.mem_cons_self i' (List.mem_cons_of_mem _ hi') k hk hk') ▸ hi')
        have e1 : (S.binds sel (i :: l)).pt ρ z k =
            (S.binds sel l).pt ρ.2 (Function.update z k ρ.1) k := by
          show Binds.pt (s := S.rd i :: (S.sc l).shape)
              ((sel i).map fun k => (k, fun c : E => c), S.binds sel l) ρ z k = _
          rw [hk]
          rfl
        rw [e1, Binds.pt_of_notMem _ _ _ hnot, Function.update_self,
          S.point_of_pub_sc l x' xo _ _ hxo i hl'.1, S.point_of_pb hx'', Function.update_self]
      · have ih := fun z' => pt_binds sel l hl'.2 hs' x' xo _ _ z' hxo i hi' k hk
        show Binds.pt (s := S.rd i₀ :: (S.sc l).shape)
            ((sel i₀).map fun k => (k, fun c : E => c), S.binds sel l) ρ z k = _
        cases sel i₀ with
        | none => exact ih z
        | some k₀ => exact ih _

end SC

/-! ## 5b. The product layer -/

namespace PL

variable {E Y P N Ξ κ : Type}
  [Field E] [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N] (L : PL E Y P N Ξ)

/-- The rounds of a product layer as rounds of a rider. sel is indexed by the coordinates of the
next point (ζ | ϱ̂) of the layer: coordinate 0 is ζ, coordinate t + 1 is the challenge of the round
that binds the variable t. -/
def binds (sel : ℕ → Option κ) : Binds κ E L.pl.shape :=
  Binds.app (s := (L.sc.sc L.ord).shape) (t := L.fin.shape)
    (L.sc.binds (fun t => sel (t + 1)) L.ord) ((sel 0).map fun k => (k, fun c : E => c), ())

theorem inj_binds (sel : ℕ → Option κ) : (L.binds sel).Inj := by
  refine Binds.Inj.app (L.sc.inj_binds _ _) ?_
  show Binds.Inj (s := [rV E]) ((sel 0).map fun k => (k, fun c : E => c), ())
  cases sel 0 with
  | none => trivial
  | some k => exact ⟨fun _ _ h => h, trivial⟩

/-- Under `OrdOK`, the variables that the layer binds are the images of the coordinates 0, .., g. -/
theorem mem_vars_binds (ho : L.OrdOK) (sel : ℕ → Option κ) {k : κ} :
    k ∈ (L.binds sel).vars ↔ ∃ t ≤ L.g, sel t = some k := by
  have hv : (L.binds sel).vars =
      (L.sc.binds (fun t => sel (t + 1)) L.ord).vars ++
        Binds.vars (s := [rV E])
          (((sel 0).map fun k => (k, fun c : E => c), ()) : Binds κ E [rV E]) :=
    Binds.vars_app (s := (L.sc.sc L.ord).shape) (t := L.fin.shape) _ _
  rw [hv, List.mem_append, SC.vars_binds, List.mem_filterMap]
  have h0 : k ∈ Binds.vars (s := [rV E])
          (((sel 0).map fun k => (k, fun c : E => c), ()) : Binds κ E [rV E]) ↔
      sel 0 = some k := by
    cases h : sel 0 with
    | none => exact ⟨fun hm => absurd hm List.not_mem_nil, fun e => by cases e⟩
    | some k₀ =>
      show k ∈ [k₀] ↔ _
      rw [List.mem_singleton]
      exact ⟨fun e => by rw [e], fun e => (Option.some.inj e).symm⟩
  rw [h0]
  constructor
  · rintro (⟨t, ht, hk⟩ | hk)
    · exact ⟨t + 1, ho.mem.1 ht, hk⟩
    · exact ⟨0, Nat.zero_le _, hk⟩
  · rintro ⟨t, ht, hk⟩
    cases t with
    | zero => exact Or.inr hk
    | succ t => exact Or.inl ⟨t, ho.mem.2 ht, hk⟩

variable [DecidableEq κ]

/-- Under `OrdOK`, where the layer's verifier does not reject (h): for t ≤ L.g (ht) with sel t =
some k (hk), the coordinate k of the point of the rider is the coordinate t of the next point of the
layer, if different coordinates t ≤ L.g have different images (hs). -/
theorem pt_binds (ho : L.OrdOK) (sel : ℕ → Option κ)
    (hs : ∀ t ≤ L.g, ∀ t' ≤ L.g, ∀ k, sel t = some k → sel t' = some k → t = t') {x : PLX N E Ξ}
    {xo : XOut N E Ξ} {ρ : Rho L.pl.shape} {p : Plains L.pl.shape} (z : κ → E)
    (h : L.pl.pub x ρ p = some xo) {t : ℕ} (ht : t ≤ L.g) {k : κ} (hk : sel t = some k) :
    (L.binds sel).pt ρ z k = xo.1.pt t := by
  obtain ⟨x₁, hx₁, hfin⟩ := Option.bind_eq_some_iff.mp
    (show ((L.sc.sc L.ord).pub (x.C, fun _ => 0, (x.pt, x.led, x.pub))
          (Rho.fst (s := (L.sc.sc L.ord).shape) (t := L.fin.shape) ρ)
          (plFst (s := (L.sc.sc L.ord).shape) (t := L.fin.shape) p)).bind
        (fun x' =>
          L.fin.pub x' (Rho.snd (s := (L.sc.sc L.ord).shape) ρ)
            (plSnd (s := (L.sc.sc L.ord).shape) p)) = some xo from h)
  obtain ⟨-, -, rfl⟩ := L.fin_some hfin
  have hp : (L.binds sel).pt ρ z =
      Binds.pt (s := [rV E]) (((sel 0).map fun k => (k, fun c : E => c), ()) : Binds κ E [rV E])
        (Rho.snd (s := (L.sc.sc L.ord).shape) (t := L.fin.shape) ρ)
        ((L.sc.binds (fun t => sel (t + 1)) L.ord).pt
          (Rho.fst (s := (L.sc.sc L.ord).shape) (t := L.fin.shape) ρ) z) :=
    Binds.pt_app (s := (L.sc.sc L.ord).shape) (t := L.fin.shape) _ _ ρ z
  rw [hp]
  generalize hz' : (L.sc.binds (fun t => sel (t + 1)) L.ord).pt
      (Rho.fst (s := (L.sc.sc L.ord).shape) (t := L.fin.shape) ρ) z = z'
  generalize Rho.snd (s := (L.sc.sc L.ord).shape) (t := L.fin.shape) ρ = ρ₂ at *
  obtain ⟨ζ, u⟩ := ρ₂
  cases t with
  | zero =>
    show Binds.pt (s := [rV E]) ((sel 0).map fun k => (k, fun c : E => c), ()) (ζ, u) z' k = ζ
    rw [hk]
    exact Function.update_self _ _ _
  | succ t =>
    have h1 : z' k = x₁.2.1 t := by
      rw [← hz']
      exact L.sc.pt_binds (fun t => sel (t + 1)) L.ord ho.nodup
        (fun i hi i' hi' k' e e' =>
          Nat.succ_injective (hs (i + 1) (ho.mem.1 hi) (i' + 1) (ho.mem.1 hi') k' e e'))
        _ _ _ _ z hx₁ t (ho.mem.2 ht) k hk
    show Binds.pt (s := [rV E]) ((sel 0).map fun k => (k, fun c : E => c), ()) (ζ, u) z' k =
      x₁.2.1 t
    cases h0 : sel 0 with
    | none => exact h1
    | some k₀ =>
      have hne : k ≠ k₀ := fun e =>
        absurd (hs (t + 1) ht 0 (Nat.zero_le _) k hk (e ▸ h0)) (Nat.succ_ne_zero t)
      show Function.update z' k₀ ζ k = x₁.2.1 t
      rw [Function.update_of_ne hne, h1]

end PL

/-! ## 6. Multilinear extensions of arrays -/

section Ext

variable {κ E : Type} [Field E] [DecidableEq κ]

/-- The extension of an array of 2^g entries, taken at the coordinates σ 0, .., σ (g - 1) of a
point: it has degree at most 1 in each variable, if these coordinates are different. -/
theorem degLE_ext_comp (g : ℕ) (v : ℕ → E) (σ : ℕ → κ)
    (hσ : ∀ t < g, ∀ t' < g, σ t = σ t' → t = t') :
    DegLE (fun _ => 1) fun z : κ → E => ext g v fun t => z (σ t) := by
  intro z k
  by_cases hk : ∃ t < g, σ t = k
  · obtain ⟨t, ht, rfl⟩ := hk
    obtain ⟨q, hq, he⟩ := degLE_ext' g v (fun t' => z (σ t')) t
    refine ⟨q, hq, fun r => ?_⟩
    rw [← he r]
    refine ext_congr_point (fun t' ht' => ?_) v
    by_cases htt : t' = t
    · subst htt
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne htt, Function.update_of_ne fun h => htt (hσ t' ht' t ht h)]
  · refine ⟨Polynomial.C (ext g v fun t => z (σ t)), by simp, fun r => ?_⟩
    rw [Polynomial.eval_C]
    refine ext_congr_point (fun t' ht' => ?_) v
    rw [Function.update_of_ne fun h => hk ⟨t', ht', h⟩]

/-- If the extension vanishes in its g variables, which are different, the array is 0. -/
theorem vanishes_ext {g : ℕ} {v : ℕ → E} {σ : ℕ → κ} (hσ : ∀ t < g, ∀ t' < g, σ t = σ t' → t = t')
    {z : κ → E} {T : List κ} (hT : ∀ t < g, σ t ∈ T)
    (h : Vanishes (fun z : κ → E => ext g v fun t => z (σ t)) z T) : ∀ X < 2 ^ g, v X = 0 := by
  classical
  intro X hX
  have h1 := h (fun j => if hj : ∃ t < g, σ t = j then cubePt g X hj.choose else z j) fun j hj => by
    show (if hj : ∃ t < g, σ t = j then cubePt g X hj.choose else z j) = z j
    rw [dif_neg fun ⟨t, ht, e⟩ => hj (e ▸ hT t ht)]
  rw [← ext_cubePt g v hX, ← h1]
  refine ext_congr_point (fun t ht => ?_) v
  have hex : ∃ t' < g, σ t' = σ t := ⟨t, ht, rfl⟩
  show cubePt g X t = if hj : ∃ t' < g, σ t' = σ t then cubePt g X hj.choose else z (σ t)
  rw [dif_pos hex, hσ _ hex.choose_spec.1 t ht hex.choose_spec.2]

omit [DecidableEq κ] in
/-- The converse: the extension of the array 0 vanishes. -/
theorem vanishes_ext_of_zero
    {g : ℕ} {v : ℕ → E} (σ : ℕ → κ) (z : κ → E) (T : List κ) (h : ∀ X < 2 ^ g, v X = 0) :
    Vanishes (fun z : κ → E => ext g v fun t => z (σ t)) z T := fun z' _ => by
  show ext g v (fun t => z' (σ t)) = 0
  rw [ext_congr (w := fun _ => 0) h]
  unfold ext
  simp

end Ext

/-! ## 7. The numbers -/

section Nums

variable {P E κ : Type} {a b : Sorts}

/-- Every error of `S.both ε'`, as a probability, is at most c, if those of the stage and the second
errors are. -/
theorem Stage.Below.both {S : Stage P E a b} {ε' : Err S.B.shape} {c : ℝ≥0∞}
    (h : S.Below c) (h' : Err.Below ε' c) : (S.both ε').Below c :=
  Err.Below.max h h'


theorem Err.max_eq_left_of_le : ∀ {s : Shape} {ε ε' : Err s}, Err.le ε' ε → Err.max ε ε' = ε
  | [], _, _, _ => rfl
  | _ :: _, (_, _), (_, _), h => Prod.ext (Nat.max_eq_left h.1) (Err.max_eq_left_of_le h.2)

theorem Err.le_app :
    ∀ {s t : Shape} {a a' : Err s} {b b' : Err t},
      Err.le a a' → Err.le b b' → Err.le (Err.app a b) (Err.app a' b')
  | [], _, _, _, _, _, _, h => h
  | _ :: _, _, (_, _), (_, _), _, _, h, h' => ⟨h.1, Err.le_app h.2 h'⟩

/-- A second list of errors below the stage's own changes nothing. -/
theorem Stage.both_eq_self (S : Stage P E a b) {ε' : Err S.B.shape} (h : Err.le ε' S.ε) :
    S.both ε' = S := by
  unfold Stage.both
  rw [Err.max_eq_left_of_le h]

theorem Stage.U_both (S : Stage P E a b) (ε' : Err S.B.shape) : (S.both ε').U = S.U := rfl
theorem Stage.D_both (S : Stage P E a b) (ε' : Err S.B.shape) : (S.both ε').D = S.D := rfl
theorem Stage.pBad_both (S : Stage P E a b) (ε' : Err S.B.shape) : (S.both ε').pBad = S.pBad := rfl
theorem Stage.pWin_both (S : Stage P E a b) (ε' : Err S.B.shape) : (S.both ε').pWin = S.pWin := rfl

end Nums

/-! ### When a second test changes no error of a sumcheck or of a product layer -/

theorem SC.err_binds_le {E Y P Ξ ι κ : Type} [Field E] [Fintype E] [DecidableEq E] [DecidableEq ι]
    (S : SC E Y P Ξ ι) (sel : ι → Option κ) (d : κ → ℕ)
    (h : ∀ i k, sel i = some k → d k ≤ S.e i + 1) :
    ∀ l : List ι, Err.le ((S.binds sel l).err d) (S.scErr l)
  | [] => trivial
  | i :: l => by
      show Err.le (s := S.rd i :: (S.sc l).shape)
        (Binds.err d (s := S.rd i :: (S.sc l).shape)
          ((sel i).map fun k => (k, fun c : E => c), S.binds sel l))
        (S.e i + 1, S.scErr l)
      cases hs : sel i with
      | none => exact ⟨Nat.zero_le _, SC.err_binds_le S sel d h l⟩
      | some k => exact ⟨h i k hs, SC.err_binds_le S sel d h l⟩

theorem PL.err_binds_le {E Y P N Ξ κ : Type} [Field E] [Fintype E] [DecidableEq E] [Fintype N]
    [DecidableEq N] (L : PL E Y P N Ξ) (sel : ℕ → Option κ) (d : κ → ℕ) (e : ℕ)
    (h : ∀ t k, sel (t + 1) = some k → d k ≤ L.sc.e t + 1) (h0 : ∀ k, sel 0 = some k → d k ≤ e) :
    Err.le ((L.binds sel).err d) (L.plErr e) := by
  have e1 : (L.binds sel).err d =
      Err.app (s := (L.sc.sc L.ord).shape) (t := L.fin.shape)
        ((L.sc.binds (fun t => sel (t + 1)) L.ord).err d)
        (Binds.err d (s := [PL.rV E]) ((sel 0).map fun k => (k, fun c : E => c), ())) :=
    Binds.err_app (s := (L.sc.sc L.ord).shape) (t := L.fin.shape) d _ _
  rw [e1]
  refine Err.le_app (s := (L.sc.sc L.ord).shape) (t := L.fin.shape) (a' := L.sc.scErr L.ord)
    (b' := (e, ())) (L.sc.err_binds_le _ d h _) ?_
  show Err.le (s := [PL.rV E])
    (Binds.err d (s := [PL.rV E]) ((sel 0).map fun k => (k, fun c : E => c), ())) (e, ())
  cases hs : sel 0 with
  | none => exact ⟨Nat.zero_le _, trivial⟩
  | some k => exact ⟨h0 k hs, trivial⟩

end Blocks
