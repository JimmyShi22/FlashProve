-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/RngCallsProps.lean: proofs of the properties of the range reduction by calls.

`props_stage` proves `Spec.props_stage` (Blocks/RngCalls.lean), stage by stage: if the parameters
meet `Par.OK` at the characteristic p of E, and 2 ≠ 0 in E (assumed throughout the file), then the
range reduction `Par.stage` has `Stage.Props` (Blocks/Stage.lean), from the relation "every key of
every call is in its table" (`Par.c0`) to "the linear claim and the one index claim are true"
(`Par.cEnd`). The characteristic is used where steps 1 to 4 of a lookup argument occur.

The words below are those of the eleven steps in the header comment of Blocks/RngCalls.lean. A call
is one lookup of many keys in one table; each call has its own lookup argument. η, η⁰, η¹: the pad
vectors of steps 1, 2 and 11. `bit`: the committed vector of the bits of the multiplicities of all
calls (step 3); B: the part of one call in it. RA: the committed vector of the arrays of the root
tests of all calls (step 7a). t_f: the part that depends on W of the end value of call f's key side;
s_f = t_f + η⁰_f: the masked scalar sent for it (step 7). LIN: a deferred claim that a form has the
value 0 (step 9). A pass (`row` in Lean names) is one phase of the lookup argument, repeated over
all calls (Blocks/StageRep.lean).

All calls share one list of deferred claims; the relation of a call still holds with any other true
list in its place (`RAt.led`; `HAt.led`, for the honest relation, asks for a copy that is good for
the list), so a step of one call preserves the relations of the others.

Notation (Blocks/RngCalls.lean, where no path is given): `RAt j f`: the relation of soundness of
call f in phase j: 0 before its lookup argument, 1 after steps 1 to 4, 2 after the point of the
degree check, 3 after the root test; `ph j k f`: in pass j, before its step k: the calls below k are
in phase j + 1, the others in phase j; `cutL j k sc`: the relations in pass j (0: steps 1 to 4; 1:
degree points; and (2, 0): before RA) before its step k; sc says whether the scalars s_f have been
sent; `cutA`: after RA has been sent; `cutR k`: the relations in the pass of the root tests before
its step k; `c0`: before the protocol; `c6`: after step 10; `d` in `Lk.Adds T d`
(Blocks/LookupStage.lean): d = (LIN, opened forms, REL); `UG Q` (Blocks/LookupStage.lean): the pads
of the groups whose rank has the property Q; `rank` (the same file): zy 0, k 1, t 2, lf 3, bt 4, uv
5, rt 6.

Limits: nothing on numbers at a parameter set; nothing on a protocol that proves the linear claim.
-/
import Blocks.RngCalls

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks.RngC.Par

open Iop Prob Finset Alg
open Blocks.Rng (Plan pre pick)
open scoped ENNReal

variable {F : Type} [Field F] (G : Par F) (E : Type) [Field E] [NeZero (2 : E)] [Fintype E]
  [DecidableEq E] [Algebra F E]

/-! ## Entries -/

theorem proj_eta (y : G.Y1 E) (j : Fin G.Cη.msg) : G.proj1 E y (G.place1 (G.iη j)) = y.1.1.2 j := by
  unfold place1 iη
  rw [Fin.addCases_left]
  rfl

theorem proj_eta0 (y : G.Y1 E) (j : Fin G.C0.msg) : G.proj1 E y (G.place1 (G.i0 j)) = y.1.2 j := by
  unfold place1 i0
  rw [Fin.addCases_right]
  rfl

/-- If η and η⁰ in y hold the pads π, every pad is at its entry. -/
theorem proj_place {y : G.Y1 E} {π : G.P0 → E} (h1 : ∀ j, y.1.1.2 j = π (G.iη j))
    (h0 : ∀ j, y.1.2 j = π (G.i0 j)) (p : G.P0) :
    G.proj1 E y (G.place1 p) = π p := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) p
  · exact (G.proj_eta E y j).trans (h1 j)
  · exact (G.proj_eta0 E y j).trans (h0 j)

theorem proj_bit (y : G.Y1 E) (i : Fin G.rowsB) (j : Fin G.Cb.msg) :
    G.proj1 E y (.inr ⟨(), i, j⟩) = (y.2 () i j).toE := rfl

theorem val_ent (y : G.Y1 E) (x : ℕ) : Form.val (G.proj1 E y) (G.ent1 E x) = G.flatBit E y.2 x := by
  unfold ent1 flatBit
  by_cases h : x / G.Cb.msg < G.rowsB ∧ 0 < G.Cb.msg
  · rw [dif_pos h, Form.val_ent, proj_bit]
    unfold nat
    rw [dif_pos h.1]
    dsimp only
    rw [dif_pos (Nat.mod_lt _ h.2)]
  · rw [dif_neg h, map_zero]
    unfold nat
    by_cases h1 : x / G.Cb.msg < G.rowsB
    · rw [dif_pos h1]
      dsimp only
      rw [dif_neg fun h2 => h ⟨h1, lt_of_le_of_lt (Nat.zero_le _) h2⟩]
    · rw [dif_neg h1]

theorem lk_B (f : ℕ) (y : G.Y1 E) :
    (G.lkT1 E f).B y = fun i θ π => G.flatBit E y.2 (G.plcB E f ((G.par E f).bIdx i θ π)) := by
  funext i θ π
  exact G.val_ent E y _

section Honest

variable [DecidableEq F]

theorem flatBit_msgBit (W : Mat F) {x : ℕ} (hx : x < G.rowsB * G.Cb.msg) :
    G.flatBit E (G.msgBit E W) x = algebraMap F E (G.bitFlat E W x) := by
  have hpos : 0 < G.Cb.msg := by
    rcases Nat.eq_zero_or_pos G.Cb.msg with h | h
    · rw [h, Nat.mul_zero] at hx
      exact absurd hx (Nat.not_lt_zero _)
    · exact h
  have h1 : x / G.Cb.msg < G.rowsB := (Nat.div_lt_iff_lt_mul hpos).2 hx
  unfold flatBit nat
  rw [dif_pos h1]
  dsimp only
  rw [dif_pos (Nat.mod_lt _ hpos)]
  show algebraMap F E (G.bitFlat E W (x / G.Cb.msg * G.Cb.msg + x % G.Cb.msg)) = _
  rw [Nat.div_add_mod']

/-- At the index of multiplicity bit number u < wBit f of call f < nc the honest bit holds that bit.
The six conditions are those of Par.OK on the table. -/
theorem flatBit_plcB {f : ℕ} (hlg : G.lgR ≤ (G.par E f).gT) (hmsg : G.Cb.msg = G.tB.msg)
    (hK : 0 < G.tB.K2) (hx : G.tB.x ≤ G.lgR) (hroom : pre (G.kB E) G.plan.nc ≤ G.tB.hB * G.tB.K2)
    (hrows : G.rowsB = 2 ^ (G.lgR - G.tB.x) * G.tB.hB) (W : Mat F) (hf : f < G.plan.nc) {u : ℕ}
    (hu : u < G.wBit E f) :
    G.flatBit E (G.msgBit E W) (G.plcB E f u) = algebraMap F E (G.bitU E W f u) := by
  have hk : 0 < G.kB E f := Nat.two_pow_pos _
  have hw : G.wBit E f = 2 ^ G.lgR * G.kB E f := by
    unfold wBit kB
    rw [← pow_add, Nat.add_sub_cancel' hlg]
  have hr : u / G.kB E f < 2 ^ (G.lgR - G.tB.x) * 2 ^ G.tB.x := by
    rw [← pow_add, Nat.sub_add_cancel hx]
    exact (Nat.div_lt_iff_lt_mul hk).2 (hw ▸ hu)
  have hm : u % G.kB E f < G.kB E f := Nat.mod_lt _ hk
  have hc : pre (G.kB E) f + u % G.kB E f < G.tB.hB * G.tB.K2 := by
    have h1 := Rng.pre_mono (G.kB E) (show f + 1 ≤ G.plan.nc from hf)
    rw [Rng.pre_succ] at h1
    omega
  have hlt : G.plcB E f u < G.rowsB * G.Cb.msg := by
    rw [hrows, hmsg]
    exact TPl.line_lt hK hr hc
  rw [G.flatBit_msgBit E W hlt]
  unfold bitFlat plcB
  rw [TPl.rowOf_line hK hc, TPl.colOf_line hK hc, Rng.pick_pre (G.kB E) _ hf hm, Nat.div_add_mod']

/-- Under the same six conditions, in range: the honest B of a call f < nc is the vector of the bits
of its multiplicities. -/
theorem flatBit_honest {f : ℕ} (hlg : G.lgR ≤ (G.par E f).gT) (hmsg : G.Cb.msg = G.tB.msg)
    (hK : 0 < G.tB.K2) (hxB : G.tB.x ≤ G.lgR) (hroom : pre (G.kB E) G.plan.nc ≤ G.tB.hB * G.tB.K2)
    (hrows : G.rowsB = 2 ^ (G.lgR - G.tB.x) * G.tB.hB) (W : Mat F) {i θ π : ℕ} (hf : f < G.plan.nc)
    (hi : i < 2 ^ (G.par E f).r) (hθ : θ < 2 ^ (G.par E f).σ) (hπ : π < 2 ^ (G.par E f).lp) :
    G.flatBit E (G.msgBit E W) (G.plcB E f ((G.par E f).bIdx i θ π)) =
      if G.bitN E f W i θ π then 1 else 0 := by
  have e : (G.par E f).bIdx i θ π =
      i * 2 ^ ((G.par E f).σ + (G.par E f).lp) + (θ * 2 ^ (G.par E f).lp + π) := by
    unfold LkPar.bIdx
    rw [Nat.add_assoc]
  have hu : θ * 2 ^ (G.par E f).lp + π < 2 ^ ((G.par E f).σ + (G.par E f).lp) := by
    rw [pow_add]
    calc θ * 2 ^ (G.par E f).lp + π < θ * 2 ^ (G.par E f).lp + 2 ^ (G.par E f).lp := by omega
      _ = (θ + 1) * 2 ^ (G.par E f).lp := by ring
      _ ≤ 2 ^ (G.par E f).σ * 2 ^ (G.par E f).lp := Nat.mul_le_mul_right _ hθ
  have hx : (G.par E f).bIdx i θ π < G.wBit E f := by
    rw [e]
    unfold wBit LkPar.gT
    rw [pow_add 2 (G.par E f).r]
    calc
      i * 2 ^ ((G.par E f).σ + (G.par E f).lp) + (θ * 2 ^ (G.par E f).lp + π) <
          i * 2 ^ ((G.par E f).σ + (G.par E f).lp) + 2 ^ ((G.par E f).σ + (G.par E f).lp) := by
        omega
      _ = (i + 1) * 2 ^ ((G.par E f).σ + (G.par E f).lp) := by ring
      _ ≤ 2 ^ (G.par E f).r * 2 ^ ((G.par E f).σ + (G.par E f).lp) := Nat.mul_le_mul_right _ hi
  rw [G.flatBit_plcB E hlg hmsg hK hxB hroom hrows W hf hx]
  unfold bitU
  obtain ⟨d1, d2, d3⟩ := (G.par E f).decode i hθ hπ
  rw [e, d1, d2, d3]
  split_ifs
  · exact map_one _
  · exact map_zero _

end Honest

/-! ## Reading and writing one call -/

section Lens

variable {N' E' F' : Type}

theorem _root_.Blocks.RngC.XL.get_put_self (x : XL N' E') (f : ℕ) (xo : LkX N' E') :
    (x.put f xo).get f = xo := by
  unfold XL.put XL.get
  dsimp only
  rw [Function.update_self]

theorem _root_.Blocks.RngC.XL.get_put_ne (x : XL N' E') {f g : ℕ} (h : g ≠ f) (xo : LkX N' E') :
    (x.put f xo).get g = { x.get g with led := xo.led } := by
  unfold XL.put XL.get
  dsimp only
  rw [Function.update_of_ne h]

theorem _root_.Blocks.RngC.XL.c_put_ne (x : XL N' E') {f g : ℕ} (h : g ≠ f) (xo : LkX N' E') :
    (x.put f xo).c g = x.c g :=
  Function.update_of_ne h _ _
theorem _root_.Blocks.RngC.XL.c_put_self (x : XL N' E') (f : ℕ) (xo : LkX N' E') :
    (x.put f xo).c f = xo :=
  Function.update_self _ _ _

theorem _root_.Blocks.RngC.IL.get_put_self (s : IL F' E') (f : ℕ) (so : LkA E') :
    (s.put f so).get f = so := by
  unfold IL.put IL.get
  dsimp only
  rw [Function.update_self]

theorem _root_.Blocks.RngC.IL.get_put_ne (s : IL F' E') {f g : ℕ} (h : g ≠ f) (so : LkA E') :
    (s.put f so).get g = { s.get g with hl := so.hl } := by
  unfold IL.put IL.get
  dsimp only
  rw [Function.update_of_ne h]

end Lens

theorem ph_self (j k : ℕ) : ph j k k = j := if_neg (Nat.lt_irrefl k)
theorem ph_succ_self (j k : ℕ) : ph j (k + 1) k = j + 1 := if_pos (Nat.lt_succ_self k)
theorem ph_succ_ne (j : ℕ) {k f : ℕ} (h : f ≠ k) : ph j (k + 1) f = ph j k f := by
  unfold ph
  by_cases h1 : f < k
  · rw [if_pos h1, if_pos (by omega)]
  · rw [if_neg h1, if_neg (by omega)]
theorem ph_zero (j f : ℕ) : ph j 0 f = j := if_neg (Nat.not_lt_zero f)
theorem ph_end (j : ℕ) {n f : ℕ} (h : f < n) : ph j n f = j + 1 := if_pos h

section Rows

variable [DecidableEq F] (pl : G.Places E)

variable {G E pl}

/-- The relation of a call reads the list of deferred claims in one clause, "all deferred claims are
true": any true list may take its place. -/
theorem RAt.led {j f : ℕ} {x : LkX G.N1 E} {y : G.Y1 E} (h : G.RAt E pl j f x y)
    {l : Ledger G.N1 E} (hl : l.True (G.proj1 E y)) :
    G.RAt E pl j f { x with led := l } y :=
  match j, h with
  | 0, h => ⟨hl, h.2⟩
  | 1, h => ⟨hl, h.2⟩
  | 2, h => ⟨hl, h.2⟩
  | _ + 3, h => ⟨hl, h.2⟩

theorem RAt.true {j f : ℕ} {x : LkX G.N1 E} {y : G.Y1 E} (h : G.RAt E pl j f x y) :
    x.led.True (G.proj1 E y) :=
  match j, h with
  | 0, h => h.1
  | 1, h => h.1
  | 2, h => h.1
  | _ + 3, h => h.1

/-- In the honest relation of a call the list and the prover's copy of it occur in three clauses,
together `HLed.Good`: any list with a copy that is good for it (`HLed.Good`) may take their places.
-/
theorem HAt.led {j f : ℕ} {a : LkA E} {π : G.P0 → E} {x : LkX G.N1 E} {y : G.Y1 E}
    (h : G.HAt E pl j f a π x y) {l : Ledger G.N1 E} {hh : HLed E} (hg : hh.Good l (G.proj1 E y)) :
    G.HAt E pl j f { a with hl := hh } π { x with led := l } y :=
  match j, h with
  | 0, ⟨h1, h2, h3, _, _, _, h7⟩ => ⟨h1, h2, h3, hg.2.1, hg.2.2, hg.1, h7⟩
  | 1, ⟨⟨⟨h1, h2, h3, _, _, _, h7⟩, hp⟩, hr⟩ => ⟨⟨⟨h1, h2, h3, hg.2.1, hg.2.2, hg.1, h7⟩, hp⟩, hr⟩
  | 2, ⟨⟨⟨⟨h1, h2, h3, _, _, _, h7⟩, hp⟩, hr⟩, hd⟩ => ⟨⟨⟨⟨h1, h2, h3, hg.2.1, hg.2.2, hg.1, h7⟩, hp⟩, hr⟩, hd⟩
  | _ + 3, ⟨⟨⟨h1, h2, h3, _, _, _, h7⟩, hp⟩, hr⟩ => ⟨⟨⟨h1, h2, h3, hg.2.1, hg.2.2, hg.1, h7⟩, hp⟩, hr⟩

theorem HAt.good {j f : ℕ} {a : LkA E} {π : G.P0 → E} {x : LkX G.N1 E}
    {y : G.Y1 E} (h : G.HAt E pl j f a π x y) : a.hl.Good x.led (G.proj1 E y) :=
  match j, h with
  | 0, ⟨_, _, _, h4, h5, h6, _⟩ => ⟨h6, h4, h5⟩
  | 1, ⟨⟨⟨_, _, _, h4, h5, h6, _⟩, _⟩, _⟩ => ⟨h6, h4, h5⟩
  | 2, ⟨⟨⟨⟨_, _, _, h4, h5, h6, _⟩, _⟩, _⟩, _⟩ => ⟨h6, h4, h5⟩
  | _ + 3, ⟨⟨⟨_, _, _, h4, h5, h6, _⟩, _⟩, _⟩ => ⟨h6, h4, h5⟩

/-- One step of a pass. T is a phase of the lookup argument of call k, which leads the call from
phase j to phase j + 1. Under the hypotheses below: on the common list, and beside the other calls,
it leads from the relations of the pass before step k to those before step k + 1. -/
theorem props_step {X : Type} {k : ℕ} (hk : k < G.plan.nc) (j : ℕ) (sc : Bool)
    (T : Stage G.P0 E ⟨X, G.Y1 E, LkA E⟩ (G.L1 E pl k).sX) (gx : XL G.N1 E → X)
    {ca : Cut G.P0 E ⟨X, G.Y1 E, LkA E⟩} {cb : Cut G.P0 E (G.L1 E pl k).sX} (hT : T.Props ca cb)
    (himp : ∀ y τ, T.B.imp y τ = y) {d : ℕ × ℕ × ℕ} (hadd : Lk.Adds T d)
    (hlen : G.lenAt E j (k + 1) =
      ((G.lenAt E j k).1 + d.1, (G.lenAt E j k).2.1 + d.2.1, (G.lenAt E j k).2.2 + d.2.2))
    (hRa : ∀ x y, ca.R (gx x) y → G.RAt E pl j k (x.get k) y)
    (hRb : ∀ xo y, G.RAt E pl (j + 1) k xo y → cb.R xo y)
    (hHa : ∀ s π x y,
      G.HAt E pl j k (IL.get (F := F) s k) π (x.get k) y → ca.Hn (s.get k) π (gx x) y)
    (hHb : ∀ a π xo y, cb.Hn a π xo y → G.HAt E pl (j + 1) k a π xo y) (hVa : ∀ s, ca.V s)
    (hz : sc = true → ∀ x ρ p xo, T.B.pub (gx x) ρ p = some xo → xo.z = (x.c k).z) :
    (T.on (a' := G.sL1 E) (b' := G.sL1 E) gx (fun x xo => x.put k xo) id (fun y _ => y)
        (fun s => s.get k) fun s so => s.put k so).Props
      (G.cutL E pl j k sc) (G.cutL E pl j (k + 1) sc) := by
  refine hT.on (fun x y τ xo hxo hR => ?_) (fun s π x y hH => ?_)
    (fun s _ => hVa _) fun _ _ _ _ => trivial
  · have e : T.B.imp (id y) τ = y := himp y τ
    rw [e]
    obtain ⟨_, hall, hcr⟩ : (x.put k xo).led.True (G.proj1 E y) ∧
        (∀ f, f < G.plan.nc → G.RAt E pl (ph j (k + 1) f) f ((x.put k xo).get f) y) ∧
        (sc = true → ∀ f, f < G.plan.nc → G.CrOK1 E pl (x.put k xo).s ((x.put k xo).c f).z y f) :=
      hR
    have hkk := hall k hk
    rw [ph_succ_self, XL.get_put_self] at hkk
    refine ⟨hRb _ _ hkk, fun ha => ?_⟩
    have hak := hRa x y ha
    refine ⟨hak.true, fun f hf => ?_, fun hs f hf => ?_⟩
    · by_cases hfk : f = k
      · subst hfk
        rw [ph_self]
        exact hak
      · have h1 := hall f hf
        rw [ph_succ_ne j hfk, XL.get_put_ne x hfk] at h1
        exact h1.led (l := x.led) hak.true
    · have h1 := hcr hs f hf
      by_cases hfk : f = k
      · subst hfk
        rw [XL.c_put_self, hz hs x _ _ xo hxo] at h1
        exact h1
      · rw [XL.c_put_ne x hfk] at h1
        exact h1
  · obtain ⟨⟨hW, hp, _, hl⟩, hall, hcr⟩ := hH
    refine ⟨hHa s π x y (by have := hall k hk; rwa [ph_self] at this), fun ρ xo _ hxo ho => ?_⟩
    have e : T.B.imp (id y) (T.H.tr (s.get k) π ρ) = y := himp y _
    rw [e] at ho
    have hko := hHb _ _ _ _ ho
    show (G.cutL E pl j (k + 1) sc).Hn (s.put k (T.H.next (s.get k) ρ)) π (x.put k xo) y
    refine ⟨⟨hW, hp, hko.good, ?_⟩, fun f hf => ?_, fun hs f hf => ?_⟩
    · show (T.H.next (s.get k) ρ).hl.len = _
      rw [hadd, hlen]
      show ((s.hl.len).1 + d.1, (s.hl.len).2.1 + d.2.1, (s.hl.len).2.2 + d.2.2) = _
      rw [hl]
    · by_cases hfk : f = k
      · subst hfk
        rw [ph_succ_self, XL.get_put_self, IL.get_put_self]
        exact hko
      · rw [ph_succ_ne j hfk, XL.get_put_ne x hfk, IL.get_put_ne s hfk]
        exact (hall f hf).led hko.good
    · have h1 := hcr hs f hf
      by_cases hfk : f = k
      · subst hfk
        show G.CrOK1 E pl x.s ((x.put f xo).c f).z y f
        rw [XL.c_put_self, hz hs x _ _ xo hxo]
        exact h1
      · show G.CrOK1 E pl x.s ((x.put k xo).c f).z y f
        rw [XL.c_put_ne x hfk]
        exact h1

/-! ## The sizes and the honest facts of one call -/

variable {p : ℕ} {WFp : Mat F → Prop}

theorem OK.wf (h : G.OK E pl p WFp) {f : ℕ} (hf : f < G.plan.nc) : (G.par E f).WF p :=
  have w := (G.pl1 f).lk_wf (E := E) (h.valid.one hf) (le_refl 1) (h.char f hf)
  { nt := w.nt, t0 := w.t0, dle := w.dle, char := w.char, ord := h.ord
    φ := fun _ => by
      show (2 ^ (G.plan.D - G.plan.k) - G.cov f) * 2 ^ (G.plan.k - G.plan.B) ≤
        2 ^ (G.plan.D - G.plan.B)
      have e : 2 ^ (G.plan.D - G.plan.B) =
          2 ^ (G.plan.D - G.plan.k) * 2 ^ (G.plan.k - G.plan.B) := by
        rw [← pow_add]
        congr 1
        have := h.valid.k_le
        have := h.Bk
        omega
      rw [e]
      exact Nat.mul_le_mul_right _ (Nat.sub_le _ _) }

theorem disj_eta :
    Disjoint (Set.range G.iη) (Set.range G.i0) := Set.disjoint_left.2 fun q hq hq' => by
  obtain ⟨a, rfl⟩ := hq
  obtain ⟨b, hb⟩ := hq'
  have h1 : G.Cη.msg + b.val = a.val := congrArg Fin.val hb
  have := a.2
  omega

theorem OK.crSub (h : G.OK E pl p WFp) :
    (Set.range fun f : Fin G.plan.nc => pl.cr f) ⊆ Set.range G.i0 := by
  rintro _ ⟨f, rfl⟩
  exact h.crIn f f.2

/-- Under `Par.OK`: the pads of the masked scalars s are disjoint from the pads that a call f < nc
uses (`used`; `apartCr`) and from those of the closing block (`apartCrCl`, below). -/
theorem OK.apartCr (h : G.OK E pl p WFp) {f : ℕ} (hf : f < G.plan.nc) :
    Disjoint (G.used E pl f) (Set.range fun f : Fin G.plan.nc => pl.cr f) :=
  disj_eta.mono (h.lkIn f hf) h.crSub
theorem OK.apartCrCl (h : G.OK E pl p WFp) :
    Disjoint (Set.range fun f : Fin G.plan.nc => pl.cr f)
      (Set.range pl.cl.aux ∪ Set.range pl.cl.opn) :=
  (disj_eta.mono h.clIn h.crSub).symm

/-- Under `Par.OK`, if all keys are in their tables (`KeysAll`): for the honest bit the facts
`Lk.TF` that the lookup argument of call f < nc needs hold. -/
theorem tf_honest (h : G.OK E pl p WFp) {f : ℕ} (hf : f < G.plan.nc) {y : G.Y1 E}
    (hK : G.plan.KeysAll y.1.1.1) (hy : y.2 = G.msgBit E y.1.1.1) :
    ((G.L1 E pl f).TF (G.lkT1 E f)) y := by
  have hD : (G.par E f).D < 2 ^ (G.par E f).lp :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h.valid.pl2'
  have h0 := (G.pl1 f).honB (E := E) (lf := 0) (r := G.plan.d f) h.valid.B_le
    (fun _ _ => le_rfl) ((G.plan.keysAll_iff_one _).1 hK f hf)
  have hpB : 0 < 2 ^ G.plan.B := by positivity
  have hB : (G.par E f).HonB ((G.pl1 f).keyT y.1.1.1) ((G.lkT1 E f).B y)
      (G.padT f) ((G.pl1 f).rowT y.1.1.1) :=
    { padKey := fun θ _ i hi hp => by
        have hc : G.cov f ≤ (i * 2 ^ G.plan.B + θ % 2 ^ G.plan.B) / 2 ^ G.plan.k :=
          of_decide_eq_true hp
        have hidx : i * 2 ^ G.plan.B + θ % 2 ^ G.plan.B < 2 ^ G.plan.D := by
          have hD' : 2 ^ G.plan.D = 2 ^ (G.plan.D - G.plan.B) * 2 ^ G.plan.B := by
            rw [← pow_add, Nat.sub_add_cancel h.valid.B_le]
          have hb : θ % 2 ^ G.plan.B < 2 ^ G.plan.B := Nat.mod_lt _ hpB
          have hi' : i < 2 ^ (G.plan.D - G.plan.B) := hi
          calc i * 2 ^ G.plan.B + θ % 2 ^ G.plan.B < i * 2 ^ G.plan.B + 2 ^ G.plan.B := by omega
            _ = (i + 1) * 2 ^ G.plan.B := by ring
            _ ≤ 2 ^ (G.plan.D - G.plan.B) * 2 ^ G.plan.B := Nat.mul_le_mul_right _ hi'
            _ = 2 ^ G.plan.D := hD'.symm
        have hlt : (i * 2 ^ G.plan.B + θ % 2 ^ G.plan.B) / 2 ^ G.plan.k <
            2 ^ (G.plan.D - G.plan.k) := by
          rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel h.valid.k_le]
          exact hidx
        show algebraMap F E (G.plan.key f y.1.1.1 (i * 2 ^ G.plan.B + θ % 2 ^ G.plan.B)) =
          ((0 % 2 ^ G.plan.d f : ℕ) : E)
        rw [G.plan.key_of_isPad (h.covPad f hf _ hc hlt), map_zero, Nat.zero_mod, Nat.cast_zero]
      rowKey := fun θ hθ i hi _ => h0.rowKey θ hθ i hi rfl
      phi := fun θ hθ => by
        have hθ' : θ < 2 ^ G.plan.B := by
          have : θ < 1 * 2 ^ G.plan.B := hθ
          omega
        have hm : 0 < 2 ^ (G.plan.k - G.plan.B) := by positivity
        have hk : 2 ^ G.plan.k = 2 ^ G.plan.B * 2 ^ (G.plan.k - G.plan.B) := by
          rw [← pow_add, Nat.add_sub_cancel' h.Bk]
        have hiff : ∀ i,
            G.padT f θ i = true ↔ G.cov f * 2 ^ (G.plan.k - G.plan.B) ≤ i := fun i => by
          unfold padT
          rw [decide_eq_true_iff, Nat.mod_eq_of_lt hθ', hk, ← Nat.div_div_eq_div_mul,
            Nat.add_comm, Nat.add_mul_div_right _ _ hpB, Nat.div_eq_of_lt hθ',
            Nat.zero_add, Nat.le_div_iff_mul_le hm]
        show G.phi f = _
        rw [Finset.filter_congr fun i _ => hiff i, Finset.range_eq_Ico, Finset.Ico_filter_le,
          Nat.card_Ico, Nat.zero_max]
        show (2 ^ (G.plan.D - G.plan.k) - G.cov f) * 2 ^ (G.plan.k - G.plan.B) =
          2 ^ (G.plan.D - G.plan.B) - _
        rw [Nat.sub_mul, ← pow_add]
        congr 2
        have := h.valid.k_le
        have := h.Bk
        omega
      bits := fun t ht θ hθ π hπ => by
        rw [G.lk_B E f y, hy]
        exact G.flatBit_honest E (h.lgRle f hf) h.tBmsg h.tBpos h.tBx h.room h.rowsBeq y.1.1.1 hf ht
          (lt_of_lt_of_le hθ (h.wf hf).nt) hπ }
  exact ⟨hB.isBits, hB.degE hD, hB.ident hD⟩

/-- Under `Par.OK`: the end value of the key side of call f, that is the extension at z of the
leaves α - key over all its keys, is a public part minus t_f. -/
theorem ext_leafK (h : G.OK E pl p WFp) (f : ℕ) (W : Mat F) (al : E) (z : ℕ → E) :
    ext ((G.par E f).D + (G.par E f).σ) ((G.par E f).leafK ((G.pl1 f).keyT W) al) z =
        G.cst E f al z - G.tval E f W z :=
  (G.pl1 f).ext_leafK (E := E) (r := G.plan.d f) h.valid.k_le h.valid.B_le (le_refl 1) W al z

/-! ## The numbers of deferred claims -/

theorem acc_succ (A : ℕ → ℕ × ℕ × ℕ) (k : ℕ) :
    acc A (k + 1) =
      ((acc A k).1 + (A k).1, (acc A k).2.1 + (A k).2.1, (acc A k).2.2 + (A k).2.2) := by
  unfold acc
  simp only [sum_range_succ]

theorem acc_zero (A : ℕ → ℕ × ℕ × ℕ) : acc A 0 = (0, 0, 0) := by
  unfold acc
  simp only [range_zero, sum_empty]

theorem length_lins (x : XL G.N E) : (G.lins E pl x).length = 4 * G.plan.nc := by
  unfold lins
  rw [List.length_flatMap]
  have : (List.map (fun f => (G.lins1 E pl x f).length) (List.range G.plan.nc)) =
      List.map (fun _ => 4) (List.range G.plan.nc) := rfl
  rw [this, List.map_const', List.sum_replicate, List.length_range, smul_eq_mul, Nat.mul_comm]

theorem mem_lins {x : XL G.N E} {f : ℕ} (hf : f < G.plan.nc)
    {g : Form G.N E} (hg : g ∈ G.lins1 E pl x f) : g ∈ G.lins E pl x :=
  List.mem_flatMap.2 ⟨f, List.mem_range.2 hf, hg⟩

/-! ## The steps of the three passes -/

theorem U14_sub (f : ℕ) : (G.st14 E pl f).U ⊆ (G.L1 E pl f).UG (· ≤ 4) := (G.L1 E pl f).st14_U_sub
theorem D14_eq (f : ℕ) : (G.st14 E pl f).D = (G.st14 E pl f).U := (G.L1 E pl f).st14_D
theorem U6_sub (f : ℕ) : (G.st6 E pl f).U ⊆ (G.L1 E pl f).UG (6 ≤ ·) := by
  rw [← (G.L1 E pl f).UG_up Sum.inl (G.proj E)]
  exact (G.L E pl f).st6r_U_sub (G.ru E f) (G.rv E f)
theorem D6_eq (f : ℕ) : (G.st6 E pl f).D = (G.st6 E pl f).U := rfl
theorem sub14 (f : ℕ) : (G.L1 E pl f).UG (· ≤ 4) ⊆ G.used E pl f :=
  (G.L1 E pl f).UG_mono fun m (hm : m ≤ 4) => by omega
theorem sub6 (f : ℕ) : (G.L1 E pl f).UG (6 ≤ ·) ⊆ G.used E pl f :=
  (G.L1 E pl f).UG_mono fun m (hm : 6 ≤ m) => by omega

theorem props_st14 [CharP E p] (h : G.OK E pl p WFp) {k : ℕ} (hk : k < G.plan.nc) :
    (G.st14 E pl k).Props (G.cutL E pl 0 k false) (G.cutL E pl 0 (k + 1) false) :=
  props_step hk 0 false (G.L1 E pl k).st14 (fun x => x.led)
    ((G.L1 E pl k).props_st14 (G.lkT1 E k) (h.wf hk) (h.pads k hk)) (G.L1 E pl k).imp_st14
    (G.L1 E pl k).adds_st14 (acc_succ (G.add14 E) k) (fun _ _ h => h) (fun _ _ h => h)
    (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) (fun _ => trivial) fun h => by cases h

theorem props_st5 (h : G.OK E pl p WFp) {k : ℕ} (hk : k < G.plan.nc) :
    (G.st5 E pl k).Props (G.cutL E pl 1 k false) (G.cutL E pl 1 (k + 1) false) :=
  props_step hk 1 false (G.L1 E pl k).st5 (fun x => x.get k)
    ((G.L1 E pl k).props_st5 (G.lkT1 E k) (h.wf hk).nt) (fun _ _ => rfl) (G.L1 E pl k).adds_st5
    rfl (fun _ _ h => h) (fun _ _ h => h) (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
    (fun _ => trivial) fun h => by cases h

/-- After the last step of a pass all calls are in the next phase: if the lengths of the list agree
(`hl`), the relations are those before the first step of the next pass. -/
theorem cutL_next (j : ℕ) (sc : Bool) (hl : G.lenAt E j G.plan.nc = G.lenAt E (j + 1) 0) :
    G.cutL E pl j G.plan.nc sc = G.cutL E pl (j + 1) 0 sc := by
  have e : ∀ f, f < G.plan.nc → ph j G.plan.nc f = ph (j + 1) 0 f :=
    fun f hf => by rw [ph_end j hf, ph_zero]
  unfold cutL
  rw [hl]
  congr 1
  · funext x y
    exact propext (and_congr Iff.rfl (and_congr (forall₂_congr fun f hf => by rw [e f hf]) Iff.rfl))
  · funext s π x y
    exact propext (and_congr Iff.rfl (and_congr (forall₂_congr fun f hf => by rw [e f hf]) Iff.rfl))

theorem disj_calls (h : G.OK E pl p WFp) {i j : ℕ} (hi : i < G.plan.nc) (hj : j < G.plan.nc)
    (hij : i ≠ j) {A B : Set G.P0} (hA : A ⊆ G.used E pl i) (hB : B ⊆ G.used E pl j) :
    Disjoint A B := (h.apart i j hi hj hij).mono hA hB

theorem props_row14 [CharP E p] (h : G.OK E pl p WFp) :
    (Stage.rep (G.st14 E pl) G.plan.nc 0).Props
      (G.cutL E pl 0 0 false) (G.cutL E pl 1 0 false) := by
  have h1 := Stage.props_rep (S := G.st14 E pl) (c := fun k => G.cutL E pl 0 k false) G.plan.nc 0 (fun j _ hj => props_st14 h (by omega)) fun i j _ hij hj =>
    ⟨disj_calls h (by omega) (by omega) (by omega)
        ((U14_sub i).trans (sub14 i)) ((U14_sub j).trans (sub14 j)),
      disj_calls (i := i) (j := j) h (by omega) (by omega) (by omega)
        (by rw [D14_eq]; exact (U14_sub i).trans (sub14 i)) ((U14_sub j).trans (sub14 j))⟩
  rw [Nat.zero_add] at h1
  have e := cutL_next (G := G) (E := E) (pl := pl) 0 false rfl
  rw [← e]
  exact h1

theorem props_row5 (h : G.OK E pl p WFp) :
    (Stage.rep (G.st5 E pl) G.plan.nc 0).Props (G.cutL E pl 1 0 false) (G.cutL E pl 2 0 false) := by
  have h1 := Stage.props_rep (S := G.st5 E pl) (c := fun k => G.cutL E pl 1 k false) G.plan.nc 0 (fun j _ hj => props_st5 h (by omega)) fun i j _ _ _ =>
    ⟨Set.empty_disjoint _, Set.empty_disjoint _⟩
  rw [Nat.zero_add] at h1
  have e := cutL_next (G := G) (E := E) (pl := pl) 1 false (by
    show _ = (_, _, _)
    rw [acc_zero]
    rfl)
  rw [← e]
  exact h1

/-! ## The steps around the passes -/

theorem props_st1 : (G.st1 E).Props (G.c0 E) (G.c1 E) := Stage.props_pads _ _
theorem props_st2 : (G.st2 E).Props (G.c1 E) (G.c2 E) := Stage.props_pads _ _

theorem props_st3 : (G.st3 E).Props (G.c2 E) (G.c3 E) := by
  have h := Stage.props_nameVec (P := G.P0) (E := E) (a := G.s2 E) (G.rBit E) (fun e => e.elim)
    (G.msgBit E) (T := Unit) (fun _ _ => ()) (fun _ _ _ => ()) (fun _ x y => (G.c2 E).R x y)
    (G.c2 E).Hn fun _ => True
  exact h

theorem props_st4 (h : G.OK E pl p WFp) : (G.st4 E).Props (G.c3 E) (G.cutL E pl 0 0 false) :=
  Stage.props_pure
    (fun _ y xo hf hR => by
      obtain rfl := Option.some.inj hf
      obtain ⟨_, hall, _⟩ := hR
      refine ⟨(G.plan.keysAll_iff_one _).2 fun f hf => ?_, rfl⟩
      have h1 := hall f hf
      rw [ph_zero] at h1
      exact ((G.pl1 f).inTable_iff
        (E := E) (lf := 0) (r := G.plan.d f) h.valid.B_le (fun _ _ => le_rfl) y.1.1.1).1 h1.2)
    (fun s π _ y hH => by
      obtain ⟨⟨⟨⟨rfl, hK⟩, hπ⟩, hπ0⟩, hy⟩ := hH
      have hp := G.proj_place E hπ hπ0
      refine ⟨_, rfl, ⟨rfl, hp, HLed.good_empty _, (acc_zero _).symm⟩,
        fun f hf => ?_, fun hs => by cases hs⟩
      rw [ph_zero]
      refine ⟨rfl, ?_, fun q _ => hp q, rfl, Ledger.true_empty _,
        ⟨rfl, rfl, rfl⟩, tf_honest h hf hK hy⟩
      show (G.initA E y.1.1.1 f).B = (G.lkT1 E f).B y
      rw [G.lk_B E f y, hy]
      rfl)
    fun _ _ => trivial

theorem val_crForm (s : ℕ → E) (f : ℕ) (y : G.Y1 E) :
    Form.val (G.proj1 E y) (G.crForm1 E pl s f) = s f - G.proj1 E y (G.place1 (pl.cr f)) :=
  Form.val_masked _ _ _

theorem props_stSc (h : G.OK E pl p WFp) :
    (G.stSc E pl).Props (G.cutL E pl 2 0 false) (G.cutL E pl 2 0 true) := by
  have h1 := Stage.props_nameScalars (P := G.P0) (E := E) (a := G.sL1 E)
    (fun f : Fin G.plan.nc => pl.cr f) h.crInj (G.valS E) (fun y q => G.proj1 E y (G.place1 q))
    (fun x y f => G.tval E f y.1.1.1 (x.c f).z) (fun _ x y => (G.cutL E pl 2 0 false).R x y)
    (G.cutL E pl 2 0 false).Hn fun _ => True
  refine Stage.Props.seq h1
    (Stage.props_pure (fun o y xo hf hR => ?_) (fun s π o y hH => ?_) fun _ _ => trivial)
    (Set.disjoint_empty _) (Set.disjoint_empty _)
  · obtain rfl := Option.some.inj hf
    obtain ⟨h1, h2, h3⟩ := hR
    refine ⟨⟨h1, h2, fun hs => by cases hs⟩, funext fun f => ?_⟩
    have h4 := h3 rfl f f.2
    unfold CrOK1 at h4
    rw [val_crForm] at h4
    have e : nat o.2 f.val = o.2 f := dif_pos f.2
    rw [← e]
    exact h4
  · obtain ⟨⟨hb, hall, _⟩, ho⟩ := hH
    refine ⟨_, rfl, hb, hall, fun _ f hf => ?_⟩
    unfold CrOK1
    rw [val_crForm]
    show nat o.2 f - G.proj1 E y (G.place1 (pl.cr f)) = G.tval E f y.1.1.1 (o.1.c f).z
    have e : nat o.2 f = o.2 ⟨f, hf⟩ := dif_pos hf
    rw [e, ho, hb.2.1]
    show G.tval E f s.W (s.a f).z + π (pl.cr f) - π (pl.cr f) = _
    have h8 := hall f hf
    rw [ph_zero] at h8
    have hz : (s.a f).z = (o.1.c f).z := h8.1.1.2.2.1
    rw [hb.1, hz, add_sub_cancel_right]

/-! ## After RA is sent -/

theorem val_entC (f x : ℕ) (y : G.Y E) :
    Form.val (G.proj E y) (G.entC E f x) = Form.val (G.proj1 E y.1) (G.entC1 E f x) := by
  unfold entC
  rw [Form.val_push]
  rfl

theorem lkT_B (f : ℕ) (y : G.Y E) : (G.lkT E f).B y = (G.lkT1 E f).B y.1 := by
  funext i θ π
  exact val_entC f _ y

/-- The lookup argument of a call after RA is the one before it, over the larger implicit part. -/
theorem up (f : ℕ) : Lk.Up (G.L1 E pl f) (G.lkT1 E f) Sum.inl (G.proj E) (G.lkT E f) Prod.fst :=
  ⟨fun _ _ => rfl, fun _ => rfl, lkT_B f⟩

theorem val_entA (y : G.Y E) (x : ℕ) : Form.val (G.proj E y) (G.entA E x) = G.flatRA E y.2 x := by
  unfold entA flatRA
  by_cases h : x / G.CA.msg < G.rowsA ∧ 0 < G.CA.msg
  · rw [dif_pos h, Form.val_ent]
    unfold nat
    rw [dif_pos h.1]
    dsimp only
    rw [dif_pos (Nat.mod_lt _ h.2)]
    rfl
  · rw [dif_neg h, map_zero]
    unfold nat
    by_cases h1 : x / G.CA.msg < G.rowsA
    · rw [dif_pos h1]
      dsimp only
      rw [dif_neg fun h2 => h ⟨h1, lt_of_le_of_lt (Nat.zero_le _) h2⟩]
    · rw [dif_neg h1]

theorem flatRA_msgRA (s : IL F E) {x : ℕ} (hx : x < G.rowsA * G.CA.msg) :
    G.flatRA E (G.msgRA E s) x = G.raFlat E s x := by
  have hpos : 0 < G.CA.msg := by
    rcases Nat.eq_zero_or_pos G.CA.msg with h | h
    · rw [h, Nat.mul_zero] at hx
      exact absurd hx (Nat.not_lt_zero _)
    · exact h
  have h1 : x / G.CA.msg < G.rowsA := (Nat.div_lt_iff_lt_mul hpos).2 hx
  unfold flatRA nat
  rw [dif_pos h1]
  dsimp only
  rw [dif_pos (Nat.mod_lt _ hpos)]
  show G.raFlat E s (x / G.CA.msg * G.CA.msg + x % G.CA.msg) = _
  rw [Nat.div_add_mod']

/-- If RA has room: in range, the honest RA holds in the part of call f the arrays of that call. -/
theorem flatRA_honest (hroom : pre (G.wRA E) G.plan.nc ≤ G.rowsA * G.CA.msg) (s : IL F E) {f u : ℕ}
    (hf : f < G.plan.nc) (hu : u < G.wRA E f) :
    G.flatRA E (G.msgRA E s) (pre (G.wRA E) f + u) = G.raVal E f (s.a f) u := by
  have hx' : pre (G.wRA E) f + u < G.rowsA * G.CA.msg := by
    have h1 := Rng.pre_mono (G.wRA E) (show f + 1 ≤ G.plan.nc from hf)
    rw [Rng.pre_succ] at h1
    omega
  rw [flatRA_msgRA s hx']
  unfold raFlat
  rw [Rng.pick_pre (G.wRA E) _ hf hu]

/-- Under `Par.OK` and the hypotheses below: the honest RA holds the honest arrays of call f. -/
theorem rah_honest (h : G.OK E pl p WFp) {s : IL F E} {f : ℕ} (hf : f < G.plan.nc)
    {x : LkX G.N E} {y : G.Y E} (hy : y.2 = G.msgRA E s)
    (hB : (s.a f).B = (G.lkT E f).B y) (hal : (s.a f).al = x.al) :
    (G.L E pl f).RAh (G.lkT E f) (G.ru E f) (G.rv E f) x y := by
  have key : ∀ π, π < (G.par E f).Pm →
      ∀ t, t < 2 * (G.par E f).NT →
        ((G.par E f).Pm - 1 - π) * (2 * (G.par E f).NT) + t < G.wRA E f ∧
        (((G.par E f).Pm - 1 - π) * (2 * (G.par E f).NT) + t) / (2 * (G.par E f).NT) =
          (G.par E f).Pm - 1 - π ∧
        (((G.par E f).Pm - 1 - π) * (2 * (G.par E f).NT) + t) % (2 * (G.par E f).NT) = t ∧
        (G.par E f).Pm - 1 - ((G.par E f).Pm - 1 - π) = π := fun π hπ t ht => by
    have hNT : 0 < 2 * (G.par E f).NT := lt_of_le_of_lt (Nat.zero_le _) ht
    refine ⟨?_, ?_, ?_, by omega⟩
    · unfold wRA
      calc
        ((G.par E f).Pm - 1 - π) * (2 * (G.par E f).NT) + t <
            ((G.par E f).Pm - 1 - π) * (2 * (G.par E f).NT) + 2 * (G.par E f).NT := by omega
        _ = ((G.par E f).Pm - 1 - π + 1) * (2 * (G.par E f).NT) := by ring
        _ ≤ (G.par E f).Pm * (2 * (G.par E f).NT) := Nat.mul_le_mul_right _ (by omega)
        _ = 2 * ((G.par E f).Pm * (G.par E f).NT) := by ring
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hNT, Nat.div_eq_of_lt ht, Nat.zero_add]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
  refine ⟨fun π hπ θ hθ => ?_, fun π hπ θ hθ => ?_⟩
  · obtain ⟨k1, k2, k3, k4⟩ :=
      key π hπ ((G.par E f).NT + θ) (by have : θ < (G.par E f).NT := hθ; omega)
    show Form.val (G.proj E y)
        (G.entA E (pre (G.wRA E) f +
            (((G.par E f).Pm - 1 - π) * (2 * (G.par E f).NT) + ((G.par E f).NT + θ)))) = _
    rw [val_entA, hy, flatRA_honest h.roomA s hf k1]
    unfold raVal
    rw [k2, k3, k4, if_neg (by omega), Nat.add_sub_cancel_left, hB, hal]
    rfl
  · obtain ⟨k1, k2, k3, k4⟩ := key π hπ θ (by have : θ < (G.par E f).NT := hθ; omega)
    show Form.val (G.proj E y)
        (G.entA E (pre (G.wRA E) f + (((G.par E f).Pm - 1 - π) * (2 * (G.par E f).NT) + θ))) = _
    rw [val_entA, hy, flatRA_honest h.roomA s hf k1]
    unfold raVal
    rw [k2, k3, k4, if_pos (show θ < (G.par E f).NT from hθ), hB, hal]
    rfl

theorem RAtR.led {j f : ℕ} {x : LkX G.N E} {y : G.Y E} (h : G.RAtR E pl j f x y)
    {l : Ledger G.N E} (hl : l.True (G.proj E y)) :
    G.RAtR E pl j f { x with led := l } y :=
  match j, h with
  | 0, h => ⟨hl, h.2⟩
  | 1, h => ⟨hl, h.2⟩
  | 2, h => ⟨hl, h.2⟩
  | _ + 3, h => ⟨hl, h.2⟩

theorem RAtR.true {j f : ℕ} {x : LkX G.N E} {y : G.Y E} (h : G.RAtR E pl j f x y) :
    x.led.True (G.proj E y) :=
  match j, h with
  | 0, h => h.1
  | 1, h => h.1
  | 2, h => h.1
  | _ + 3, h => h.1

theorem HAtR.led {j f : ℕ} {a : LkA E} {π : G.P0 → E} {x : LkX G.N E} {y : G.Y E}
    (h : G.HAtR E pl j f a π x y) {l : Ledger G.N E} {hh : HLed E} (hg : hh.Good l (G.proj E y)) :
    G.HAtR E pl j f { a with hl := hh } π { x with led := l } y :=
  match j, h with
  | 0, ⟨⟨⟨h1, h2, h3, _, _, _, h7⟩, hp⟩, hr⟩ => ⟨⟨⟨h1, h2, h3, hg.2.1, hg.2.2, hg.1, h7⟩, hp⟩, hr⟩
  | 1, ⟨⟨⟨h1, h2, h3, _, _, _, h7⟩, hp⟩, hr⟩ => ⟨⟨⟨h1, h2, h3, hg.2.1, hg.2.2, hg.1, h7⟩, hp⟩, hr⟩
  | 2, ⟨⟨⟨⟨⟨h1, h2, h3, _, _, _, h7⟩, hp⟩, hr⟩, hd⟩, hra⟩ =>
    ⟨⟨⟨⟨⟨h1, h2, h3, hg.2.1, hg.2.2, hg.1, h7⟩, hp⟩, hr⟩, hd⟩, hra⟩
  | _ + 3, ⟨⟨⟨h1, h2, h3, _, _, _, h7⟩, hp⟩, hr⟩ =>
    ⟨⟨⟨h1, h2, h3, hg.2.1, hg.2.2, hg.1, h7⟩, hp⟩, hr⟩

theorem HAtR.good {j f : ℕ} {a : LkA E} {π : G.P0 → E} {x : LkX G.N E}
    {y : G.Y E} (h : G.HAtR E pl j f a π x y) : a.hl.Good x.led (G.proj E y) :=
  match j, h with
  | 0, ⟨⟨⟨_, _, _, h4, h5, h6, _⟩, _⟩, _⟩ => ⟨h6, h4, h5⟩
  | 1, ⟨⟨⟨_, _, _, h4, h5, h6, _⟩, _⟩, _⟩ => ⟨h6, h4, h5⟩
  | 2, ⟨⟨⟨⟨⟨_, _, _, h4, h5, h6, _⟩, _⟩, _⟩, _⟩, _⟩ => ⟨h6, h4, h5⟩
  | _ + 3, ⟨⟨⟨_, _, _, h4, h5, h6, _⟩, _⟩, _⟩ => ⟨h6, h4, h5⟩

theorem props_stRA : (G.stRA E).Props (G.cutL E pl 2 0 true) (G.cutA E pl) := by
  have h := Stage.props_nameVec (P := G.P0) (E := E) (a := G.sL1 E) (G.rRA E) (fun e => e.elim)
    (G.msgRA E) (T := Unit) (fun _ _ => ()) (fun _ _ _ => ())
    (fun _ x y => (G.cutL E pl 2 0 true).R x y) (G.cutL E pl 2 0 true).Hn fun _ => True
  exact h

theorem crOK_iff (s : ℕ → E) (z : ℕ → E) (y : G.Y E) (f : ℕ) :
    G.CrOK E pl s z y f ↔ G.CrOK1 E pl s z y.1 f := by
  unfold CrOK CrOK1 crForm crForm1
  rw [Form.val_masked, Form.val_masked]
  exact Iff.rfl

/-- Under `Par.OK`. The forms are carried to the entries with RA: every relation is kept, and the
honest RA holds the honest arrays. -/
theorem props_stUp (h : G.OK E pl p WFp) : (G.stUp E).Props (G.cutA E pl) (G.cutR E pl 0) :=
  Stage.props_pure
    (fun x y xo hf hR => by
      obtain rfl := Option.some.inj hf
      obtain ⟨hled, hall, hcr⟩ := hR
      refine ⟨⟨((up (pl := pl) 0).led y x.led).1 hled,
          fun f hf => ?_,
          fun _ f hf => (crOK_iff _ _ y f).1 (hcr f hf)⟩,
        rfl⟩
      have h1 := hall f hf
      rw [ph_zero] at h1 ⊢
      exact Lk.r8_of_up (up f) h1)
    (fun s π x y hH => by
      obtain ⟨⟨⟨hW, hp, hg, hl⟩, hall, hcr⟩, hy⟩ := hH
      refine ⟨_, rfl, ⟨hW, hp, HLed.Good.push Sum.inl hg, hl⟩, fun f hf => ?_,
        fun f hf => (crOK_iff _ _ y f).2 (hcr rfl f hf)⟩
      have h1 := hall f hf
      rw [ph_zero] at h1 ⊢
      have h8 : (G.L E pl f).H8 (G.lkT E f) (G.L E pl f).allPads (s.get f) π
          ((x.get f).push Sum.inl) y := by
        rw [(G.L1 E pl f).allPads_up]
        exact Lk.h8_up (up f) h1
      exact ⟨h8, rah_honest h hf hy h8.1.1.1.2.1 h8.1.1.2.1⟩)
    fun _ _ => trivial

/-- Under `Par.OK`: all properties of the root test of a call k < nc, on the common list and beside
the other calls. -/
theorem props_st6 (h : G.OK E pl p WFp) {k : ℕ} (hk : k < G.plan.nc) :
    (G.st6 E pl k).Props (G.cutR E pl k) (G.cutR E pl (k + 1)) := by
  have hlen : G.lenAt E 2 (k + 1) =
      ((G.lenAt E 2 k).1 + 1,
        (G.lenAt E 2 k).2.1 + 3 * (G.par E k).Pm,
        (G.lenAt E 2 k).2.2 + 1) := by
    show (_, _, _) = _
    rw [acc_succ]
    simp only [← Nat.add_assoc]
    rfl
  refine ((G.L E pl k).props_st6r
      (G.lkT E k) (G.ru E k) (G.rv E k) ((G.L1 E pl k).rt_up _ _ (h.pads k hk).rt) (h.wf hk).nt).on
    (fun x y τ xo hxo hR => ?_) (fun s π x y hH => ?_) (fun _ _ => trivial) fun _ _ _ _ => trivial
  · have e : ((G.L E pl k).st6r (G.ru E k) (G.rv E k)).B.imp (id y) τ = y :=
      (G.L E pl k).imp_st6r _ _ y τ
    rw [e]
    obtain ⟨_, hall, hcr⟩ : (x.put k xo).led.True (G.proj E y) ∧
        (∀ f, f < G.plan.nc → G.RAtR E pl (ph 2 (k + 1) f) f ((x.put k xo).get f) y) ∧
        (∀ f, f < G.plan.nc → G.CrOK E pl (x.put k xo).s ((x.put k xo).c f).z y f) := hR
    have hkk := hall k hk
    rw [ph_succ_self, XL.get_put_self] at hkk
    refine ⟨hkk, fun ha => ?_⟩
    have hak : G.RAtR E pl 2 k (x.get k) y := ha
    refine ⟨hak.true, fun f hf => ?_, fun f hf => ?_⟩
    · by_cases hfk : f = k
      · subst hfk
        rw [ph_self]
        exact hak
      · have h1 := hall f hf
        rw [ph_succ_ne 2 hfk, XL.get_put_ne x hfk] at h1
        exact h1.led (l := x.led) hak.true
    · have h1 := hcr f hf
      by_cases hfk : f = k
      · subst hfk
        rw [XL.c_put_self, ((G.L E pl f).pub_st6r _ _ hxo).2.1] at h1
        exact h1
      · rw [XL.c_put_ne x hfk] at h1
        exact h1
  · obtain ⟨⟨hW, hp, _, hl⟩, hall, hcr⟩ := hH
    refine ⟨by have := hall k hk; rwa [ph_self] at this, fun ρ xo _ hxo ho => ?_⟩
    have e : ((G.L E pl k).st6r (G.ru E k) (G.rv E k)).B.imp
          (id y) (((G.L E pl k).st6r (G.ru E k) (G.rv E k)).H.tr (s.get k) π ρ) = y :=
      (G.L E pl k).imp_st6r _ _ y _
    rw [e] at ho
    have hko : G.HAtR E pl 3 k
        (((G.L E pl k).st6r (G.ru E k) (G.rv E k)).H.next (s.get k) ρ) π xo y := ho
    show (G.cutR E pl (k + 1)).Hn
      (s.put k (((G.L E pl k).st6r (G.ru E k) (G.rv E k)).H.next (s.get k) ρ)) π (x.put k xo) y
    refine ⟨⟨hW, hp, hko.good, ?_⟩, fun f hf => ?_, fun f hf => ?_⟩
    · show (((G.L E pl k).st6r (G.ru E k) (G.rv E k)).H.next (s.get k) ρ).hl.len = _
      rw [(G.L E pl k).adds_st6r, hlen]
      show ((s.hl.len).1 + 1, (s.hl.len).2.1 + 3 * (G.par E k).Pm, (s.hl.len).2.2 + 1) = _
      rw [hl]
    · by_cases hfk : f = k
      · subst hfk
        rw [ph_succ_self, XL.get_put_self, IL.get_put_self]
        exact hko
      · rw [ph_succ_ne 2 hfk, XL.get_put_ne x hfk, IL.get_put_ne s hfk]
        exact (hall f hf).led hko.good
    · have h1 := hcr f hf
      by_cases hfk : f = k
      · subst hfk
        show G.CrOK E pl x.s ((x.put f xo).c f).z y f
        rw [XL.c_put_self, ((G.L E pl f).pub_st6r _ _ hxo).2.1]
        exact h1
      · show G.CrOK E pl x.s ((x.put k xo).c f).z y f
        rw [XL.c_put_ne x hfk]
        exact h1

theorem props_row6 (h : G.OK E pl p WFp) :
    (Stage.rep (G.st6 E pl) G.plan.nc 0).Props (G.cutR E pl 0) (G.cutR E pl G.plan.nc) := by
  have h1 := Stage.props_rep (S := G.st6 E pl) (c := fun k => G.cutR E pl k) G.plan.nc 0 (fun j _ hj => props_st6 h (by omega)) fun i j _ hij hj =>
    ⟨disj_calls h (by omega) (by omega) (by omega)
        ((U6_sub i).trans (sub6 i)) ((U6_sub j).trans (sub6 j)),
      disj_calls h (by omega) (by omega) (by omega)
        ((U6_sub i).trans (sub6 i)) ((U6_sub j).trans (sub6 j))⟩
  rw [Nat.zero_add] at h1
  exact h1

/-- The four LIN of call f hold exactly if the end form of its key side has the value (public part)
- (s_f - η⁰_f) and its two claims on ~bit and its degree claim hold (`CB4`, `CB5`, `CDEG`). -/
theorem lins1_zero_iff (x : XL G.N E) (f : ℕ) (y : G.Y E) :
    (∀ g ∈ G.lins1 E pl x f, Form.val (G.proj E y) g = 0) ↔
    Form.val (G.proj E y) (x.c f).Cend =
      G.cst E f (x.c f).al (x.c f).z - Form.val (G.proj E y) (G.crForm E pl x.s f) ∧
    ((G.L E pl f).CB4 (G.lkT E f)) (x.get f) y ∧
    ((G.L E pl f).CB5 (G.lkT E f)) (x.get f) y ∧
    ((G.L E pl f).CDEG (G.lkT E f)) (x.get f) y := by
  unfold lins1
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, map_sub,
    Form.val_const, (G.par E f).val_bForm, (G.par E f).val_degForm, sub_eq_zero]
  refine and_congr ⟨fun h => ?_, fun h => ?_⟩ Iff.rfl
  · rw [h]
    ring
  · rw [h]
    ring

theorem props_st7 (h : G.OK E pl p WFp) : (G.st7 E pl).Props (G.cutR E pl G.plan.nc) (G.c5 E pl) :=
  Stage.props_pure
    (fun x y xo hf hR => by
      obtain rfl := Option.some.inj hf
      obtain ⟨hled, hk⟩ := hR
      obtain ⟨h1, h2⟩ := (Ledger.true_addLins _ _ _).1 hled
      refine ⟨h1, fun f hf => ?_, hk⟩
      rw [ph_end 2 hf]
      obtain ⟨e1, e2, e3, e4⟩ := (lins1_zero_iff x f y).1 fun g hg => h2 g (mem_lins hf hg)
      refine ⟨h1, fun _ => ?_, e2, e3, e4⟩
      show Form.val (G.proj E y) (x.c f).Cend =
        ext ((G.par E f).D + (G.par E f).σ)
          ((G.par E f).leafK ((G.pl1 f).keyT y.1.1.1.1) (x.c f).al) (x.c f).z
      have hk' : Form.val (G.proj E y) (G.crForm E pl x.s f) = G.tval E f y.1.1.1.1 (x.c f).z :=
        hk f hf
      rw [ext_leafK h, e1, hk'])
    (fun s π x y hH => by
      obtain ⟨⟨hW, hp, hg, hl⟩, hall, hcr⟩ := hH
      have h10 : ∀ f, f < G.plan.nc →
          (G.L E pl f).H10 (G.lkT E f) (G.L E pl f).allPads (s.get f) π
            (x.get f) y := fun f hf => by
        have := hall f hf
        rwa [ph_end 2 hf] at this
      have hz : ∀ g ∈ G.lins E pl x, Form.val (G.proj E y) g = 0 := fun g hg => by
        obtain ⟨f, hf, hg⟩ := List.mem_flatMap.1 hg
        have hf' := List.mem_range.1 hf
        obtain ⟨_, hend, h4, h5, h6⟩ := h10 f hf'
        refine (lins1_zero_iff x f y).2 ⟨?_, h4, h5, h6⟩ g hg
        have e : Form.val (G.proj E y) (x.c f).Cend =
            ext ((G.par E f).D + (G.par E f).σ)
              ((G.par E f).leafK ((G.pl1 f).keyT y.1.1.1.1) (x.c f).al) (x.c f).z := hend.2
        rw [e, ext_leafK h, hcr f hf']
      refine ⟨_, rfl, ?_, hcr, hW, fun f hf => (h10 f hf).1.2.2.1⟩
      refine (hg.addLins hz).honLedger ?_ (G.plN E pl) pl.cl (fun k => hp _) fun o => hp _
      rw [HLed.len_addLins, hl, length_lins]
      rfl)
    fun _ _ => trivial

theorem props_st8 (h : G.OK E pl p WFp) : (G.st8 E pl).Props (G.c5 E pl) (G.c6 E pl) :=
  (Closing.props_stage (E := E) (G.nL E) (G.plN E pl) pl.cl h.auxInj h.opnInj h.auxOpn).on
    (fun _ _ _ _ _ hR => ⟨hR.1, fun hin => ⟨hin, hR.2⟩⟩)
    (fun _ _ _ _ hH => ⟨hH.1, fun _ _ _ _ ho => ⟨ho, hH.2⟩⟩)
    (fun _ _ => trivial) fun _ _ _ _ => trivial

/-! ## Steps 1 to 10 -/

theorem mem_row14 {q : G.P0} (hq : q ∈ (Stage.rep (G.st14 E pl) G.plan.nc 0).U) :
    ∃ j, j < G.plan.nc ∧ q ∈ (G.L1 E pl j).UG (· ≤ 4) := by
  obtain ⟨j, _, hj, hq⟩ := Stage.mem_rep_U.1 hq
  exact ⟨j, by omega, U14_sub j hq⟩

theorem mem_row14D {q : G.P0} (hq : q ∈ (Stage.rep (G.st14 E pl) G.plan.nc 0).D) :
    ∃ j, j < G.plan.nc ∧ q ∈ (G.L1 E pl j).UG (· ≤ 4) := by
  obtain ⟨j, _, hj, hq⟩ := Stage.mem_rep_D.1 hq
  rw [D14_eq] at hq
  exact ⟨j, by omega, U14_sub j hq⟩

theorem mem_row6 {q : G.P0} (hq : q ∈ (Stage.rep (G.st6 E pl) G.plan.nc 0).U) :
    ∃ j, j < G.plan.nc ∧ q ∈ (G.L1 E pl j).UG (6 ≤ ·) := by
  obtain ⟨j, _, hj, hq⟩ := Stage.mem_rep_U.1 hq
  exact ⟨j, by omega, U6_sub j hq⟩

theorem mem_row6D {q : G.P0} (hq : q ∈ (Stage.rep (G.st6 E pl) G.plan.nc 0).D) :
    ∃ j, j < G.plan.nc ∧ q ∈ (G.L1 E pl j).UG (6 ≤ ·) := by
  obtain ⟨j, _, hj, hq⟩ := Stage.mem_rep_D.1 hq
  exact ⟨j, by omega, U6_sub j hq⟩

theorem not_mem_row5 {q : G.P0} : q ∉ (Stage.rep (G.st5 E pl) G.plan.nc 0).U := fun hq => by
  obtain ⟨j, _, _, hq⟩ := Stage.mem_rep_U.1 hq
  exact hq

theorem not_mem_row5D {q : G.P0} : q ∉ (Stage.rep (G.st5 E pl) G.plan.nc 0).D := fun hq => by
  obtain ⟨j, _, _, hq⟩ := Stage.mem_rep_D.1 hq
  exact hq

/-- Under `Par.OK`, at the characteristic p of E: all properties of steps 1 to 10, from "every key
of every call is in its table" to "the linear claim is true, and the scalars s_f are the true ones".
-/
theorem props_stA [CharP E p] (h : G.OK E pl p WFp) : (G.stA E pl).Props (G.c0 E) (G.c6 E pl) := by
  have h78 := (props_st7 h).seq (props_st8 h) (Set.empty_disjoint _) (Set.empty_disjoint _)
  have m78 : ∀ q,
      q ∈ ((G.st7 E pl).seq (G.st8 E pl)).U → q ∈ Set.range pl.cl.aux ∪ Set.range pl.cl.opn :=
    fun q hq => hq.elim (fun h => h.elim) id
  have d6 : ∀ q, (∃ j, j < G.plan.nc ∧ q ∈ G.used E pl j) → q ∉ ((G.st7 E pl).seq (G.st8 E pl)).U :=
    fun q ⟨j, hj, hq⟩ hq' => Set.disjoint_left.1 (h.apartCl j hj) hq (m78 q hq')
  have up : ∀ {q : G.P0}, (∃ j, j < G.plan.nc ∧ q ∈ (G.L1 E pl j).UG (6 ≤ ·)) →
      ∃ j, j < G.plan.nc ∧ q ∈ G.used E pl j :=
    fun ⟨j, hj, hq⟩ => ⟨j, hj, sub6 j hq⟩
  have h68 := (props_row6 h).seq h78 (Set.disjoint_left.2 fun q hq => d6 q (up (mem_row6 hq)))
    (Set.disjoint_left.2 fun q hq => d6 q (up (mem_row6D hq)))
  have m68 : ∀ q, q ∈ ((Stage.rep (G.st6 E pl) G.plan.nc 0).seq ((G.st7 E pl).seq (G.st8 E pl))).U →
      (∃ j, j < G.plan.nc ∧ q ∈ (G.L1 E pl j).UG (6 ≤ ·)) ∨
      q ∈ Set.range pl.cl.aux ∪ Set.range pl.cl.opn :=
    fun q hq => hq.elim (fun h => Or.inl (mem_row6 h)) fun h => Or.inr (m78 q h)
  have hU8 := (props_stUp h).seq h68 (Set.empty_disjoint _) (Set.empty_disjoint _)
  have hR8 :=
    (props_stRA (G := G) (E := E) (pl := pl)).seq hU8 (Set.empty_disjoint _) (Set.empty_disjoint _)
  have mR8 : ∀ q, q ∈
        ((G.stRA E).seq
          ((G.stUp E).seq
            ((Stage.rep (G.st6 E pl) G.plan.nc 0).seq ((G.st7 E pl).seq (G.st8 E pl))))).U →
      (∃ j, j < G.plan.nc ∧ q ∈ (G.L1 E pl j).UG (6 ≤ ·)) ∨
      q ∈ Set.range pl.cl.aux ∪ Set.range pl.cl.opn := fun q hq =>
    hq.elim (fun h => h.elim) fun hq => hq.elim (fun h => h.elim) (m68 q)
  have mS : ∀ q, q ∈ (G.stSc E pl).U → q ∈ Set.range fun f : Fin G.plan.nc => pl.cr f := fun q hq =>
    hq.elim id fun h => h.elim
  have dS : ∀ q, q ∈ (Set.range fun f : Fin G.plan.nc => pl.cr f) →
      q ∉ ((G.stRA E).seq
          ((G.stUp E).seq
            ((Stage.rep (G.st6 E pl) G.plan.nc 0).seq
              ((G.st7 E pl).seq (G.st8 E pl))))).U := fun q hq hq' => by
    rcases mR8 q hq' with ⟨j, hj, h1⟩ | h1
    · exact Set.disjoint_left.1 (h.apartCr hj) (sub6 j h1) hq
    · exact Set.disjoint_left.1 h.apartCrCl hq h1
  have hS8 := (props_stSc h).seq hR8 (Set.disjoint_left.2 fun q hq => dS q (mS q hq))
    (Set.disjoint_left.2 fun q hq => dS q (mS q hq))
  have h58 := (props_row5 h).seq hS8 (Set.disjoint_left.2 fun q hq => absurd hq not_mem_row5)
    (Set.disjoint_left.2 fun q hq => absurd hq not_mem_row5D)
  have d14 : ∀ q, (∃ j, j < G.plan.nc ∧ q ∈ (G.L1 E pl j).UG (· ≤ 4)) →
      q ∉ ((Stage.rep (G.st5 E pl) G.plan.nc 0).seq
          ((G.stSc E pl).seq
            ((G.stRA E).seq
              ((G.stUp E).seq
                ((Stage.rep (G.st6 E pl) G.plan.nc 0).seq ((G.st7 E pl).seq (G.st8 E pl))))))).U :=
      fun q ⟨i, hi, hq⟩ hq' => by
    rcases hq' with h1 | h1 | h1
    · exact not_mem_row5 h1
    · exact Set.disjoint_left.1 (h.apartCr hi) (sub14 i hq) (mS q h1)
    · rcases mR8 q h1 with ⟨j, hj, h2⟩ | h2
      · by_cases hij : i = j
        · subst hij
          exact Set.disjoint_left.1
            ((G.L1 E pl i).disj_UG (h.pads i hi) (Q := (· ≤ 4))
              (Q' := (6 ≤ ·)) fun m hm => by omega)
            hq h2
        · exact Set.disjoint_left.1 (h.apart i j hi hj hij) (sub14 i hq) (sub6 j h2)
      · exact Set.disjoint_left.1 (h.apartCl i hi) (sub14 i hq) h2
  have h48 := (props_row14 h).seq h58 (Set.disjoint_left.2 fun q hq => d14 q (mem_row14 hq))
    (Set.disjoint_left.2 fun q hq => d14 q (mem_row14D hq))
  have h38 := (props_st4 h).seq h48 (Set.empty_disjoint _) (Set.empty_disjoint _)
  have h28 := (props_st3 (G := G) (E := E)).seq h38 (Set.empty_disjoint _) (Set.empty_disjoint _)
  have h18 := (props_st2 (G := G) (E := E)).seq h28 (Set.empty_disjoint _) (Set.empty_disjoint _)
  exact (props_st1 (G := G) (E := E)).seq h18 (Set.empty_disjoint _) (Set.empty_disjoint _)

/-! ## The merge of the index claims -/

/-- The index claim of call f says that the scalar s_f is the true one. -/
theorem holds_idxOf (x : Keep E) {f : ℕ} (y : G.Y E) (η : Fin G.C1.msg → E) :
    (G.idxOf E pl x f).Holds (y, η) ↔ G.CrOK E pl x.2 (x.1 f) y f := by
  unfold MG.Idx.Holds CrOK
  have h1 : (G.M E pl).forms.val (y, η) (G.idxOf E pl x f).f =
      Form.val (G.proj E y) (G.crForm E pl x.2 f) := by
    show Form.val (G.rdEnd E (y, η)) (Form.push Sum.inl (G.crForm E pl x.2 f)) = _
    rw [Form.val_push]
    rfl
  have h2 : mle ((G.M E pl).colSum (G.idxOf E pl x f).g (y, η)) (G.idxOf E pl x f).ψ =
      G.tval E f y.1.1.1.1 (x.1 f) := by
    have h3 := MG.mle_colSum_eq G.plan.h G.plan.k (G.gpsi E x.1 f).1 (G.gpsi E x.1 f).2
      fun q c => algebraMap F E (y.1.1.1.1 q c)
    show mle (fun c : Fin G.plan.k → Bool =>
          ∑ r : Fin G.plan.h, (G.gpsi E x.1 f).1 r * algebraMap F E (y.1.1.1.1 r.val (num c)))
        (G.gpsi E x.1 f).2 = _
    rw [h3]
    unfold tval
    refine sum_congr rfl fun q hq => sum_congr rfl fun c _ => ?_
    have e1 : nat (G.gpsi E x.1 f).1 q = (G.pl1 f).gAll 0 (x.1 f) q := dif_pos (mem_range.1 hq)
    have e2 : eqN G.plan.k 0 (nat (G.gpsi E x.1 f).2) c =
        eqN G.plan.k 0 ((G.pl1 f).psi 0 (x.1 f)) c :=
      Rng.eqN_shift G.plan.k 0 0 (fun t ht => by
        rw [Nat.zero_add]
        exact dif_pos ht) c
    rw [e1, e2]
  rw [h1, h2]

/-- Under `Par.OK`: all properties of η¹ and the merge of the index claims, from "the linear claim
is true, and the scalars s_f are the true ones" to "the linear claim and the one index claim are
true". -/
theorem props_stM (h : G.OK E pl p WFp) :
    (G.stM E pl).Props ((G.c6 E pl).mapP Sum.inl) (G.cEnd E pl) := by
  have hsm := (G.M E pl).props_padsMerge (Fin G.plan.nc) (Forms.ofForm_ok _ _)
    (List.nodup_finRange _) (fun v => List.mem_finRange v) h.mgOnce Sum.inr
    (Q := Set.range Sum.inr) h.mgIn (fun _ => True)
    (⟨fun x y₀ => ∃ η, ∀ j, (x j).Holds (y₀, η),
      fun a π x y₀ =>
        ∀ η, (∀ j, η j = π (Sum.inr j)) →
          (G.M E pl).HiI (Fin G.plan.nc) (Set.range Sum.inr) a π x (y₀, η),
      fun _ => True⟩ : Cut G.Pd E
        ⟨Fin G.plan.nc → (G.M E pl).Idx,
          G.Y E,
          MG.StI E (Fin G.plan.h) (Fin G.plan.k) (Fin G.plan.nc)⟩)
    (fun x y₀ η h => ⟨η, h⟩) (fun a π x y₀ η h hη => h η hη) fun _ _ => trivial
  have himp : ∀ (y : G.Y E) τ, ((G.M E pl).stPadsMerge (Fin G.plan.nc) Sum.inr G.vars).B.imp y τ =
      (y, (((G.M E pl).stPadsMerge (Fin G.plan.nc) Sum.inr G.vars).B.imp y τ).2) := fun y τ =>
    Prod.ext (by
      show (((G.M E pl).mergeC (Fin G.plan.nc) G.vars).imp _ _).1 = y
      rw [(G.M E pl).imp_mergeC]
      rfl) rfl
  refine Stage.Props.on hsm (fun x y τ a _ hR => ?_) (fun z π x y hH => ?_)
    (fun _ _ => trivial) fun _ _ _ _ => trivial
  · refine ⟨?_, fun hc => ⟨?_, fun f hf => ?_⟩⟩
    · show a.Holds (((G.M E pl).stPadsMerge (Fin G.plan.nc) Sum.inr G.vars).B.imp y τ)
      rw [himp]
      exact hR.2
    · have h1 : Form.val
            (G.rdEnd E (y, (((G.M E pl).stPadsMerge (Fin G.plan.nc) Sum.inr G.vars).B.imp y τ).2))
            (Form.push Sum.inl x.1) = 0 := hR.1
      rw [Form.val_push] at h1
      exact h1
    · obtain ⟨η, hη⟩ := hc
      exact (holds_idxOf x.2 y η).1 (hη ⟨f, hf⟩)
  · obtain ⟨hl, hk, hW, hzs⟩ := hH
    refine ⟨fun η hη => ⟨fun j => ?_, ?_, ?_, fun j => (holds_idxOf x.2 y η).2 (hk j j.2)⟩,
      fun ρ a _ _ hO => ⟨?_, ?_⟩⟩
    · show (G.gpsi E x.2.1 j).1 = (G.gpsi E z.2.2 j).1 ∧ (G.gpsi E x.2.1 j).2 = (G.gpsi E z.2.2 j).2
      unfold gpsi
      rw [hzs j j.2]
      exact ⟨rfl, rfl⟩
    · funext q c
      show algebraMap F E (y.1.1.1.1 q.val (num c)) = algebraMap F E (z.2.1 q.val (num c))
      rw [hW]
    · rintro _ ⟨j, rfl⟩
      show Form.val (G.rdEnd E (y, η)) (Form.ent (G.placeEnd (Sum.inr j))) = π (Sum.inr j)
      rw [Form.val_ent]
      exact hη j
    · show Form.val (G.rdEnd E (y, _)) (Form.push Sum.inl x.1) = 0
      rw [Form.val_push]
      exact hl
    · have hO' : (G.M E pl).HoI (Set.range Sum.inr) _ π a
          (((G.M E pl).stPadsMerge (Fin G.plan.nc) Sum.inr G.vars).B.imp y _) := hO
      rw [himp] at hO'
      exact hO'

/-- `Spec.props_stage`: all properties of the range reduction by calls. -/
theorem props_stage : Spec.props_stage G E pl := fun p _ WFp h => by
  have hUm : (G.stM E pl).U ⊆ Set.range Sum.inr := by
    show ((G.M E pl).stPadsMerge (Fin G.plan.nc) Sum.inr G.vars).U ⊆ _
    rw [MG.U_padsMerge]
    exact h.mgIn
  have hd : ∀ A : Set G.P0,
      Disjoint (Sum.inl '' A : Set G.Pd)
        (G.stM E pl).U := fun A => Set.disjoint_left.2 fun q hq hq' => by
    obtain ⟨a, _, rfl⟩ := hq
    obtain ⟨b, hb⟩ := hUm hq'
    cases hb
  exact ((props_stA h).mapP Sum.inl_injective).seq (props_stM h) (hd _) (hd _)

end Rows

end Blocks.RngC.Par
