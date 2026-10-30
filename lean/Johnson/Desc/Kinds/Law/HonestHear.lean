-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HonestHear.lean.
WHAT IT DOES NOT SHOW. That a kind's own summand, start form and end term meet the conditions that
are asked here; that the ledger which the verifier makes is Fresh; that the prover's program sends
these rounds. Nothing on soundness, on probabilities or on hiding.
WHAT IT IS. THE HONEST ROUNDS OF ONE MASKED SUMCHECK, AS HeadParts.lean HEARS IT (heardBy). Letters
in front: the call (lead, z, ends), the start form C, a Fresh ledger, the lead's scalars, the target
T (the start form's public part behind the lead's laying), the hiding coefficients, the summand with
its sum, muT and tq (for each eps the true round polynomial behind the challenges in front), whose
run is a Chain from muT + eps T to the masked summand at the challenges. Then FOR ALL eps,
challenges and end values (canonical writings) THERE ARE rounds t (z.size + 3 of them, canonical)
SUCH THAT: they are Shaped (one for one of the make that the table's rounds say: each
made of scalars and drawn elements alone, as many as its entry says; all that is drawn is among eps
and the challenges); the part's reader takes them, with just these
letters; their moves ARE the run of tq;
heardBy returns on t ++ rest for every rest, leaves rest, and leaves a Fresh ledger; and the one
form that the sumcheck leaves (rowForm) is worth 0 in EVERY world that gives the start form the sum
and the own slots the hiding coefficients, at every end term and kept form that make up the summand
at the challenges. THE ROUNDS STAND IN FRONT OF THE WORLD: a kind's world is read off a later
ledger.
It puts together Part/MaskedSumHonest.lean (honest_read), Law/Returns.lean (heardBy_returns) and
Part/MaskedSumRow.lean (rowForm_zero).

-/
import Mathlib
import Johnson.Desc.Part.MaskedSumRow
import Johnson.Desc.Kinds.Law.Returns

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE oneE addE mulE subE okE)
open OnBytes.Model (Aff Fork Reading World)
open Polynomial
open OnBytes.Desc.First.P1 (Chain honest hid psiProd)
open Part.MaskedSum (Var Call Ends readAll leadScalars ownSlots movesOf rowForm challenges
  roundsOfRun honest_read rowForm_zero)

/-- The rounds t are, one for one, of the make that the table's rounds Rs say: each is made of
scalars and drawn elements alone (rvOf: no position, no matrix entry, no digest is drawn), as many
as its entry says, and all that is drawn is in the list D. -/
def Shaped (D : List E) : List Fmt.RoundView → List Round → Prop :=
  List.Forall₂ fun r R => ∃ s d, r = Part.MaskedSum.rvOf s d ∧ s.length = R.sent ∧
    d.length = R.drawn ∧ ∀ x ∈ d, x ∈ D

theorem Shaped.mono {D D' : List E} {t : List Fmt.RoundView} {Rs : List Round} (h : Shaped D t Rs)
    (hD : ∀ x ∈ D, x ∈ D') : Shaped D' t Rs :=
  List.Forall₂.imp (fun _ _ ⟨s, d, e, a, b, c⟩ => ⟨s, d, e, a, b, fun x hx => hD x (c x hx)⟩) h

theorem Shaped.append {D : List E} {a b : List Fmt.RoundView} {Ra Rb : List Round} (ha : Shaped D a Ra)
    (hb : Shaped D b Rb) : Shaped D (a ++ b) (Ra ++ Rb) := List.rel_append ha hb

theorem shaped_one (s d : List E) (R : Round) (h1 : s.length = R.sent) (h2 : d.length = R.drawn) :
    Shaped d [Part.MaskedSum.rvOf s d] [R] :=
  List.Forall₂.cons ⟨s, d, rfl, h1, h2, fun _ h => h⟩ List.Forall₂.nil

theorem shaped_nil (D : List E) : Shaped D [] [] := List.Forall₂.nil

theorem shaped_vars (D : List E) : ∀ (l : List (List E × E)) (Rs : List Round),
    l.length = Rs.length → (∀ R ∈ Rs, R.sent = 2 ∧ R.drawn = 1) →
    (∀ x ∈ l, x.1.length = 2 ∧ x.2 ∈ D) → Shaped D (Part.MaskedSum.roundsRV l) Rs
  | [], [], _, _, _ => List.Forall₂.nil
  | x :: l, R :: Rs, hl, hR, hx =>
    List.Forall₂.cons ⟨x.1, [x.2], rfl, by rw [(hx x (by simp)).1, (hR R (by simp)).1],
      by rw [(hR R (by simp)).2]; rfl,
      fun y hy => by rw [List.mem_singleton.mp hy]; exact (hx x (by simp)).2⟩
      (shaped_vars D l Rs (by simpa using hl) (fun R' h => hR R' (by simp [h]))
        fun y h => hx y (by simp [h]))
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl

theorem lens_two : ∀ (vs : List Var) (l : List (List E × E)), Part.MaskedSum.Lens vs l →
    (∀ v ∈ vs, v.d = 3) → l.length = vs.length ∧ ∀ x ∈ l, x.1.length = 2
  | [], [], _, _ => ⟨rfl, fun x hx => by simp at hx⟩
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim
  | v :: vs, x :: l, h, hd => by
    obtain ⟨a, b⟩ := lens_two vs l h.2.2 fun u hu => hd u (by simp [hu])
    have h3 := hd v (by simp)
    have h1 := h.1
    refine ⟨by simp [a], fun y hy => ?_⟩
    rcases List.mem_cons.mp hy with e | e
    · rw [e]
      omega
    · exact b y e

/-- A sumcheck's rounds, whole, against the table's. -/
theorem shaped_run (ld : List E) (mu eps : E) (l : List (List E × E)) (values : List E)
    (m n0 ends : Nat) (hl : l.length = m + 1) (h2 : ∀ x ∈ l, x.1.length = 2)
    (h0 : ld.length + 1 = n0) (hv : values.length = ends) :
    Shaped (eps :: l.map (·.2)) (roundsOfRun ld mu eps l values)
      (⟨"PSC epsilon", n0, 1, false, 0⟩ :: (List.replicate m ⟨"PSC round", 2, 1, false, 0⟩ ++
        [⟨"PSC Y", 2, 1, true, 0⟩, ⟨"PSC values", ends, 0, false, 0⟩])) := by
  unfold roundsOfRun
  refine List.Forall₂.cons ⟨_, _, rfl, by rw [List.length_append, ← h0]; rfl, rfl, fun x hx => by
    rw [List.mem_singleton.mp hx]
    exact List.mem_cons_self ..⟩ ?_
  have e : List.replicate m (⟨"PSC round", 2, 1, false, 0⟩ : Round) ++
      [⟨"PSC Y", 2, 1, true, 0⟩, ⟨"PSC values", ends, 0, false, 0⟩] =
      (List.replicate m (⟨"PSC round", 2, 1, false, 0⟩ : Round) ++ [⟨"PSC Y", 2, 1, true, 0⟩]) ++
        [⟨"PSC values", ends, 0, false, 0⟩] := by simp
  rw [e]
  refine Shaped.append (shaped_vars _ l _ (by simp [hl]) (fun R hR => ?_) fun x hx =>
    ⟨h2 x hx, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨x, hx, rfl⟩)⟩)
    ((shaped_one values [] _ hv rfl).mono fun x hx => by simp at hx)
  rcases List.mem_append.mp hR with h | h
  · rw [(List.mem_replicate.mp h).2]
    exact ⟨rfl, rfl⟩
  · rw [List.mem_singleton.mp h]
    exact ⟨rfl, rfl⟩

/-- **THE HONEST ROUNDS OF ONE MASKED SUMCHECK, AS heardBy HEARS IT.** -/
theorem heardBy_honest (lead : Nat) (C : Array Hid → Form) (z : Point) {ends : Nat}
    (he : 1 ≤ ends) {F : Fork} {m : Nat} (ld : List E) (hld : ld.length = lead)
    (hF : Fresh F (ld.length + (ownSlots (callOf lead z ends).all + ends + m))) (T : E)
    (hT : ∀ Fa, hide ld F [] = some (hidOf F.next ld, Fa, []) →
      Fa.publicPart (C (hidOf F.next ld)) = some T)
    (hcoef : ℕ → K) (S : List K → K) (sigma muT : K) (tq : K → List K → K[X])
    (hCh : ∀ (eps : K) (rs : List K),
      rs.length = ((callOf lead z ends).all.map (Var.wt Reading.gl)).length →
      Chain ((callOf lead z ends).all.map (Var.wt Reading.gl)) (honest (tq eps) [] rs)
        (muT + eps * Reading.gl.val T)
        (hid ((callOf lead z ends).all.map (Var.wt Reading.gl)) hcoef rs + eps * S rs +
          eps * (Reading.gl.val T - sigma) *
            psiProd ((callOf lead z ends).all.map (Var.wt Reading.gl)) rs))
    (eps : E) (rsE values : List E) (hr : rsE.length = z.size + 1) (hv : values.length = ends)
    (okl : ∀ x ∈ ld, okE x = true) (oke : okE eps = true) (okr : ∀ x ∈ rsE, okE x = true)
    (okv : ∀ x ∈ values, okE x = true) :
    ∃ (t : List Fmt.RoundView) (l : List (List E × E)),
      Shaped (eps :: rsE) t (⟨"PSC epsilon", lead + 1, 1, false, 0⟩ ::
        (List.replicate z.size ⟨"PSC round", 2, 1, false, 0⟩ ++
          [⟨"PSC Y", 2, 1, true, 0⟩, ⟨"PSC values", ends, 0, false, 0⟩])) ∧
      t.length = z.size + 3 ∧ Canonical t ∧
      readAll (callOf lead z ends) t = some ⟨ofK muT, eps, l, values⟩ ∧
      leadScalars (callOf lead z ends) t = some ld ∧ l.map (·.2) = rsE ∧
      movesOf Reading.gl (callOf lead z ends).all l (addE (ofK muT) (mulE eps T)) =
        honest (tq (Reading.gl.val eps)) [] (rsE.map Reading.gl.val) ∧
      (∀ rest, ∃ (es : Array Hid) (Fa F1 : Fork),
        hide ld F [] = some (hidOf F.next ld, Fa, []) ∧
        heardBy lead C z ends F (t ++ rest) = some ((hidOf F.next ld,
          { r := (challenges (callOf lead z ends)
              (heardRec (C (hidOf F.next ld)) T ⟨ofK muT, eps, l, values⟩ (callOf lead z ends)
                (F.next + ld.length))).toArray,
            ends := es,
            psc := some (heardRec (C (hidOf F.next ld)) T ⟨ofK muT, eps, l, values⟩
              (callOf lead z ends) (F.next + ld.length)) }), F1, rest) ∧
        F1.next = F.next + ld.length + ownSlots (callOf lead z ends).all + ends ∧
        F1.ns = F.ns ∧ Fresh F1 m) ∧
      ∀ (W : World K) (S0 : E) (kept : Form),
        (C (hidOf F.next ld)).value Reading.gl W = sigma →
        (∀ i, i < ownSlots (callOf lead z ends).all → W.slot (F.next + ld.length + i) = hcoef i) →
        S (rsE.map Reading.gl.val) = Reading.gl.val S0 + kept.value Reading.gl W →
        (rowForm (heardRec (C (hidOf F.next ld)) T ⟨ofK muT, eps, l, values⟩ (callOf lead z ends)
          (F.next + ld.length)) S0 kept).value Reading.gl W = 0 := by
  have hk := shape_callOf lead z he
  have hvs : (z.toList.map (Var.point · 3)).length = z.size := by
    rw [List.length_map, Array.length_toList]
  have hall : ((callOf lead z ends).all.map (Var.wt Reading.gl)).length = z.size + 1 := by
    rw [List.length_map]
    show (z.toList.map (Var.point · 3) ++ [Var.point zeroE 3]).length = _
    rw [List.length_append, hvs]
    rfl
  have hch := hCh (Reading.gl.val eps) (rsE.map Reading.gl.val)
    (by rw [List.length_map, hr, hall])
  have hc0 : Reading.gl.val (addE (ofK muT) (mulE eps T)) =
      muT + Reading.gl.val eps * Reading.gl.val T := by
    rw [Reading.gl.add, Reading.gl.mul]
    show rd (ofK muT) + _ = _
    rw [rd_ofK]
  obtain ⟨l, b1, b2, b3, b4, b5, b6, b7⟩ := honest_read Reading.gl ofK rd_ofK lead
    (z.toList.map (Var.point · 3)) ⟨2, ends⟩ hk ld hld (ofK muT) eps T rsE values hv _ _
    (by rw [hc0]; exact hch) (OnBytes.Desc.First.P1.honest_chal _ _ [])
  have hlen : (roundsOfRun ld (ofK muT) eps l values).length = z.size + 3 := by
    rw [b6, hvs]
  obtain ⟨_, _, _, _, _, _, _, hvr, _⟩ := Part.MaskedSum.readAll_spec b1
  have hlens : Part.MaskedSum.Lens (callOf lead z ends).all l :=
    Part.MaskedSum.lens_of_read hvr (Part.MaskedSum.two_le_all hk)
  have hd3 : ∀ v ∈ (callOf lead z ends).all, v.d = 3 := by
    intro v hv'
    have hm : v ∈ z.toList.map (Var.point · 3) ++ [Var.point zeroE 3] := hv'
    rcases List.mem_append.mp hm with h | h
    · obtain ⟨x, _, rfl⟩ := List.mem_map.mp h
      rfl
    · rw [List.mem_singleton.mp h]
      rfl
  obtain ⟨hl1, hl2⟩ := lens_two _ l hlens hd3
  have hl3 : l.length = z.size + 1 := by
    rw [hl1]
    show (z.toList.map (Var.point · 3) ++ [Var.point zeroE 3]).length = _
    rw [List.length_append, hvs]
    rfl
  refine ⟨roundsOfRun ld (ofK muT) eps l values, l,
    b3 ▸ shaped_run ld (ofK muT) eps l values z.size (lead + 1) ends hl3 hl2 (by rw [hld]) hv, hlen,
    b7 (fun x => okE x = true) okE_ofK okl (okE_ofK _) oke okr okv, b1, b2, b3, b4,
    fun rest => ?_, fun W S0 kept hC hslots hend => ?_⟩
  · obtain ⟨T', es, Fa, F1, c1, c2, c3, c4, c5, c6⟩ := heardBy_returns lead C z he hlen b2 b1 hv hF
      (fun Fa h => ⟨T, hT Fa h⟩) rest
    have hTT : T' = T := by
      rw [hT Fa c1] at c2
      exact (Option.some.inj c2).symm
    subst hTT
    exact ⟨es, Fa, F1, c1, c3, c4, c5, c6⟩
  · refine rowForm_zero Reading.gl (callOf lead z ends).all hcoef S sigma W _ l S0 kept rfl hlens
      rfl ?_ hC hslots ?_
    · have b5' : Reading.gl.val (Part.MaskedSum.after (callOf lead z ends).all l
          (addE (ofK muT) (mulE eps T))) = _ := b5
      refine b5'.trans ?_
      show _ = hid _ hcoef ((l.map (·.2)).map Reading.gl.val) +
        Reading.gl.val eps * S ((l.map (·.2)).map Reading.gl.val) +
        Reading.gl.val eps * (Reading.gl.val T - sigma) *
          psiProd _ ((l.map (·.2)).map Reading.gl.val)
      rw [b3]
    · show S ((l.map (·.2)).map Reading.gl.val) = _
      rw [b3]
      exact hend

end VerifiableInference.Desc.Kinds.Head.Law
