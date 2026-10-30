-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/Norms.lean: THE LAYERS' OWN ROUNDS (K4): hearNorms RETURNS
(OnBytes/Desc/First/K4/Hear.lean: the points; the norms' sums and their squares' product layer; the
row products and their token sumcheck). A general law: nothing is evaluated.

  rowsNorms, slotsNorms   the rows of K4's table that it hears; the slots that it takes.
  optPoint_tape, foldl_inv, shown_normsStart   a point drawn in the first group alone; the start
                  form of the squares' layer names slots of the convolution sums alone.
  NormsLeft       what it leaves: sizes of the points and powers; slots by number; the token
                  sumcheck is open; WHICH SLOTS ARE FILLED: of those that it takes all but the token
                  sumcheck's own.
  **hearNorms_returns**   room for its slots, a tape of its rows' shape, four comparisons of the
                  plan's numbers, the lookup's depth is at least the plan's number la, the three
                  readings of the lookup's points return, and ONE TEST ON SAMPLED VALUES, under the
                  refusal's name "internal-g-merged-point": it returns, with NormsLeft. By a reading
                  of the lookup's own text that test is no chance event: it should hold at every
                  record that the lookup returns; no law says so here.

Limits. A conditional law. Nothing on values beyond the named test. Nothing on soundness,
completeness or hiding.

-/
import Johnson.Desc.First.K4.Returns.Kit
import OnBytes.Tie.Pv.Tail.EndClaimsB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.Model OnBytes.Model.Layer OnBytes.K.Kc D6.Ret
open OnBytes.PscRun (Sized Filled)

/-- The rows of K4's table that hearNorms hears: its numbers 1 to 3. -/
def rowsNorms (P : Pub) (g : Nat) : List Rd :=
  [pointRd .zero P.y.h.lt] ++
    ((if g == 0 then [pointRd .zero (P.y.ls + P.y.h.lt)] else []) ++
      ((if g == 0 then [pointRd .zero (P.y.lPd - P.y.ls)] else []) ++
        ([batchRd (ledNS P.y.h.xl * P.y.NI) (ledNS P.y.h.xl)] ++
          ([pointRd .join P.rd.lNI] ++
            (layerRds P.rd.muV ++
              ([batchRd (ledNP P.y.h.xl * P.y.NI) (ledNP P.y.h.xl * P.y.NI)] ++
                masked P.y.h.lt 2 2 (ledNO P.y.h.xl * P.y.NI)))))))

/-- The slots that hearNorms takes. -/
def slotsNorms (P : Pub) : Nat :=
  ledNS P.y.h.xl * P.y.NI + ((1 + (2 * P.rd.muV + (2 + 2))) +
    (ledNP P.y.h.xl * P.y.NI + (1 + (1 + (2 * P.y.h.lt + (2 + ledNO P.y.h.xl * P.y.NI))))))

/-- A point that is drawn in the first group alone. -/
theorem optPoint_tape (b : Bool) {n : Nat} {t : Tape}
    (hT : TapeOf (if b = true then [pointRd .zero n] else []) t) (F : Fork) (u : Tape) :
    ∃ a, (if b = true then engFl.point .zero n else pure #[]) F (t ++ u) = some (a, F, u) ∧
      a.size = if b = true then n else 0 := by
  cases b with
  | true => exact point_tape rfl hT F u
  | false =>
    obtain rfl := tape_nil hT
    exact ⟨#[], rfl, rfl⟩

/-- A fold keeps what each step keeps. -/
theorem foldl_inv {α β : Type} (Q : β → Prop) (f : β → α → β) : ∀ (l : List α) (b : β), Q b →
    (∀ b x, x ∈ l → Q b → Q (f b x)) → Q (l.foldl f b)
  | [], _, hb, _ => hb
  | x :: l, b, hb, h =>
    foldl_inv Q f l _ (h b x (List.mem_cons_self ..) hb)
      fun b y hy => h b y (List.mem_cons_of_mem _ hy)

/-- The start form of the squares' layer names slots of the convolution sums alone. -/
theorem shown_normsStart {G : Fork} (y : Lay) (sW : Nat) (gp rhoI PV : Array E)
    (h : ∀ i, i < ledNS y.h.xl * y.NI → sW + i < G.next ∧ Filled G (sW + i)) :
    Shown G (normsStart y sW gp rhoI PV).1 := by
  unfold normsStart
  dsimp only
  refine foldl_inv (Shown G) _ _ _ (shown_const G _) fun C i hi hC => ?_
  refine shown_foldl (fun s => Aff.slot (sW + ledNS y.h.xl * i + s)) _ _ _ hC fun s hs => ?_
  have hi' := List.mem_range.1 hi
  have hs' := List.mem_range.1 hs
  have hb : ledNS y.h.xl * i + s < ledNS y.h.xl * y.NI := by
    have : ledNS y.h.xl * (i + 1) ≤ ledNS y.h.xl * y.NI := Nat.mul_le_mul_left _ hi'
    rw [Nat.mul_succ] at this
    omega
  have := h _ hb
  rw [← Nat.add_assoc] at this
  exact shown_slot this.1 this.2

/-- What hearNorms leaves. F: the ledger in front; G: behind. -/
structure NormsLeft (P : Pub) (g : Nat) (fo : Forest.Heard) (ztF : Array E) (F G : Fork)
    (H : Heard) : Prop where
  fo : H.fo = fo
  ztF : H.ztF = ztF
  tT : H.tT = none
  pv : H.PV.size = P.y.h.lt
  ze : H.ZE.size = if (g == 0) = true then P.y.ls + P.y.h.lt else 0
  tkh : H.tkh.size = if (g == 0) = true then P.y.lPd - P.y.ls else 0
  sW : H.sW = F.next
  gp : H.gp.size = ledNS P.y.h.xl
  sums : ∀ i, i < ledNS P.y.h.xl * P.y.NI → Filled G (F.next + i)
  wplR : H.wpl.r.size = P.rd.muV
  wplL : H.wpl.sL = F.next + ledNS P.y.h.xl * P.y.NI + (1 + (2 * P.rd.muV + 2))
  wplS : H.wpl.sR = H.wpl.sL + 1
  wplF : Filled G H.wpl.sL ∧ Filled G H.wpl.sR
  sPv : H.sPv = F.next + ledNS P.y.h.xl * P.y.NI + (1 + (2 * P.rd.muV + (2 + 2)))
  prods : ∀ i, i < ledNP P.y.h.xl * P.y.NI → Filled G (H.sPv + i)
  omV : H.omV.size = ledNP P.y.h.xl * P.y.NI
  tvOpen : Open H.tV.p G
  tvIn : H.tV.p.first + taken H.tV.p ≤ G.next
  tvCl : H.tV.sCl = H.sPv + ledNP P.y.h.xl * P.y.NI
  tvClF : Filled G H.tV.sCl
  tvFirst : H.tV.p.first = H.tV.sCl + 1
  tvEnd : H.tV.sEnd = H.tV.sCl + (1 + (1 + (2 * P.y.h.lt + 2)))
  tvEnds : ∀ i, i < ledNO P.y.h.xl * P.y.NI → Filled G (H.tV.sEnd + i)
  tvStart : H.tV.p.start = Aff.slot H.tV.sCl
  tvR : H.tV.r.size = P.y.h.lt
  /-- of the slots that it takes just the token sumcheck's own are free -/
  marks : ∀ j, F.next ≤ j → j < G.next →
    (Filled G j ↔ ¬ (H.tV.p.first ≤ j ∧ j < H.tV.sEnd))

/-- **hearNorms returns.** Z, ends, ztF: what the three readings of the lookup's points return. -/
theorem hearNorms_returns (P : Pub) (g : Nat) (fo : Forest.Heard) {F : Fork} {k : Nat}
    (hR : Room F (slotsNorms P + k)) {t : Tape} (hT : TapeOf (rowsNorms P g) t) (u : Tape)
    -- the plan's numbers
    (hNS : ledNS P.y.h.xl ≠ 0) (hNP : ledNP P.y.h.xl * P.y.NI ≠ 0)
    (hNO : 1 ≤ ledNO P.y.h.xl * P.y.NI) (hmu : P.rd.muV ≤ P.rd.lNI + P.y.lPd + P.y.h.lt)
    -- what the lookup hands over: sizes
    (hdepth : P.y.h.la ≤ fo.shape.dT) {Z ztF : Array E} {ends : Array (Array E)}
    (hZ : (lastOf fo.zx P.y.h.la).toOption = some Z)
    (hE : (fo.zk.mapM fun zk => (lastOf zk P.y.h.la).toOption) = some ends)
    (hzt : (lastOf fo.zx P.y.h.lt).toOption = some ztF)
    -- the test on sampled values: "internal-g-merged-point"
    (vM : ends.all (· == Z) = true) :
    ∃ H G, hearNorms engFl P g fo F (t ++ u) = some (H, G, u) ∧ Room G k ∧ Below F G ∧
      G.next = F.next + slotsNorms P ∧ NormsLeft P g fo ztF F G H := by
  unfold rowsNorms at hT
  unfold slotsNorms at hR
  obtain ⟨t1, r1, rfl, h1, hT⟩ := tape_append hT
  obtain ⟨t2, r2, rfl, h2, hT⟩ := tape_append hT
  obtain ⟨t3, r3, rfl, h3, hT⟩ := tape_append hT
  obtain ⟨t4, r4, rfl, h4, hT⟩ := tape_append hT
  obtain ⟨t5, r5, rfl, h5, hT⟩ := tape_append hT
  obtain ⟨t6, r6, rfl, h6, hT⟩ := tape_append hT
  obtain ⟨t7, t8, rfl, h7, h8⟩ := tape_append hT
  simp only [List.append_assoc]
  obtain ⟨PV, a1, a1s⟩ := point_tape (r := .zero) rfl h1 F
    (t2 ++ (t3 ++ (t4 ++ (t5 ++ (t6 ++ (t7 ++ (t8 ++ u)))))))
  obtain ⟨ZE, a2, a2s⟩ := optPoint_tape (g == 0) h2 F
    (t3 ++ (t4 ++ (t5 ++ (t6 ++ (t7 ++ (t8 ++ u))))))
  obtain ⟨tkh, a3, a3s⟩ := optPoint_tape (g == 0) h3 F (t4 ++ (t5 ++ (t6 ++ (t7 ++ (t8 ++ u)))))
  obtain ⟨x4, G4, b1, b2, b3, b4, b5, b6⟩ := claimsBatch_tape (k := (1 + (2 * P.rd.muV + (2 + 2))) +
    (ledNP P.y.h.xl * P.y.NI + (1 + (1 + (2 * P.y.h.lt + (2 + ledNO P.y.h.xl * P.y.NI))))) + k)
    (by refine hR.mono ?_; omega) hNS h4 (t5 ++ (t6 ++ (t7 ++ (t8 ++ u))))
  obtain ⟨rhoI, a5, a5s⟩ := point_tape (r := .join) rfl h5 G4 (t6 ++ (t7 ++ (t8 ++ u)))
  obtain ⟨L, G6, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := levelIn_tape (F := G4)
    (mu := P.rd.muV)
    (k := ledNP P.y.h.xl * P.y.NI + (1 + (1 + (2 * P.y.h.lt + (2 + ledNO P.y.h.xl * P.y.NI)))) + k)
    (by refine b3.mono ?_; omega)
    (shown_normsStart P.y F.next (powers x4 (ledNS P.y.h.xl)) rhoI PV fun i hi =>
      ⟨by omega, b6 i hi⟩)
    (normsStart P.y F.next (powers x4 (ledNS P.y.h.xl)) rhoI PV).2 (orderDefault P.rd.muV)
    (by simp [orderDefault])
    (fun v hv => by
      have hv' : v < P.rd.muV := by simpa [orderDefault] using hv
      refine ⟨hv', ?_⟩
      show _ < (rhoI ++ Array.replicate P.y.lPd _ ++ PV).size
      simp only [Array.size_append, Array.size_replicate, a5s, a1s]
      omega) h6 (t7 ++ (t8 ++ u))
  obtain ⟨x7, G7, d1, d2, d3, d4, d5, d6⟩ := claimsBatch_tape (F := G6)
    (k := (1 + (1 + (2 * P.y.h.lt + (2 + ledNO P.y.h.xl * P.y.NI)))) + k)
    (by refine c2.mono ?_; omega) hNP h7 (t8 ++ u)
  obtain ⟨tV, G8, eps, e1, -, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, -, e13, e14, e15⟩ :=
    tscIn_tape (F := G7) (k := k) PV (Nat.le_of_eq a1s.symm) hNO (by omega)
      (by refine d3.mono ?_; omega) h8 u
  have B48 : Below G4 G8 := (c3.trans d4).trans e5
  have B68 : Below G6 G8 := d4.trans e5
  have l1 : L.sL < G6.next := by omega
  have l2 : L.sR < G6.next := by omega
  refine ⟨{ fo := fo, PV := PV, ZE := ZE, tkh := tkh, ztF := ztF, sW := F.next,
            gp := powers x4 (ledNS P.y.h.xl), wpl := L, sPv := G6.next,
            omV := powers x7 (ledNP P.y.h.xl * P.y.NI), tV := tV }, G8, ?_, e4,
    b4.trans B48, by unfold slotsNorms; omega, ?_⟩
  · unfold hearNorms
    refine bindR a1 ?_
    refine bindIte a2 ?_
    refine bindIte a3 ?_
    refine bindR (mustR (by simpa using hdepth) _ _) ?_
    refine bindR (needR hZ _ _) ?_
    refine bindR (needR hE _ _) ?_
    refine bindR (mustR vM _ _) ?_
    refine bindR (needR hzt _ _) ?_
    refine bindR b1 ?_
    refine bindR b2 ?_
    refine bindR a5 ?_
    refine bindR c1 ?_
    refine bindR d1 ?_
    refine bindR d2 ?_
    refine bindR e1 ?_
    rfl
  · exact
      { fo := rfl, ztF := rfl, tT := rfl, pv := a1s, ze := a2s, tkh := a3s, sW := rfl
        gp := OnBytes.Tie.Pv.Tail.Port.powers_size _ _
        sums := fun i hi => (B48.same _ (by omega)).2 (b6 i hi)
        wplR := c9, wplL := by rw [c5, b5], wplS := c6
        wplF := ⟨(B68.same _ l1).2 c7, (B68.same _ l2).2 c8⟩
        sPv := by show G6.next = _; rw [c4, b5]
        prods := fun i hi => (e5.same _ (by show G6.next + i < G7.next; omega)).2 (d6 i hi)
        omV := OnBytes.Tie.Pv.Tail.Port.powers_size _ _
        tvOpen := e2, tvIn := e3, tvCl := by rw [e6, d5], tvClF := by rw [e6]; exact e7
        tvFirst := by rw [e8, e6], tvEnd := by rw [e9, e6], tvEnds := e11
        tvStart := by rw [e13, e6], tvR := e14
        marks := fun j h1 h2 => by
          show Filled G8 j ↔ ¬ (tV.p.first ≤ j ∧ j < tV.sEnd)
          by_cases q1 : j < G4.next
          · have e : F.next + (j - F.next) = j := by omega
            have hf := b6 (j - F.next) (by omega)
            rw [e] at hf
            exact ⟨fun _ hc => by omega, fun _ => (B48.same j q1).2 hf⟩
          · by_cases q2 : j < G6.next
            · exact ⟨fun _ hc => by omega, fun _ => (B68.same j q2).2 (c10 j (by omega) q2)⟩
            · by_cases q3 : j < G7.next
              · have e : G6.next + (j - G6.next) = j := by omega
                have hf := d6 (j - G6.next) (by omega)
                rw [e] at hf
                exact ⟨fun _ hc => by omega, fun _ => (e5.same j q3).2 hf⟩
              · exact tsc_marks e2 e7 e8 e10 e11 e15 j (by omega) h2 }

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.optPoint_tape
#print axioms OnBytes.Desc.First.K4.Rt.foldl_inv
#print axioms OnBytes.Desc.First.K4.Rt.shown_normsStart
#print axioms OnBytes.Desc.First.K4.Rt.hearNorms_returns
