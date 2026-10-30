-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/KeyPsc.lean: the written zero-knowledge sumcheck, as a step, with its soundness.

The zero-knowledge sumcheck of OnBytes/Iop/Psc.lean tests nothing: in each round the verifier
computes the one coefficient that is not sent, and at the end it hands on a row and one claim for
each shown map. This file makes a step (OnBytes/Slice/KeyStep.lean) of its written rounds. The
step's next state is what the run hands on, computed by the function of
OnBytes/Slice/KeyPscRun.lean, which has the program's text over the field. The step's test is that
function's own test of sizes.

Soundness (psc_sem). All sent messages are fixed, so each mask entry has a value and the summand's
maps are functions of a point. The values are a parameter here; whoever uses the statement takes
them from the decodings of sent words, which rests on each word's decoding to one message at most.
If the claim before the step is false (the summand's sum plus the value of the claim's mask form is
not the target), then, but for the counted verifier messages, what is handed on does not hold: the
row is false, or a claim on a shown map is.

This is a proof of our own. It is not the library's theorem on its sumcheck
(Cb/Ld/LdPsc.lean: Spec.psc_sound_at), whose rounds send all coefficients and whose points are
nested pairs. The argument is the same. The error counts are the library's: 1 in the first round;
d - 1 in the round of a variable whose polynomials have d coefficients; the summand's degree in the
round of Y; 0 in the round of the shown values. Each count is of values in the field, times the
number in the law of the format's sampler. In the round of Y the written round draws no 0; the count
is of all values in the field at which a polynomial vanishes, so it also bounds those that can be
drawn.

How it is proved. The polynomial of the sumcheck is a tower (OnBytes/Slice/KeyPscF.lean): the hiding
polynomial plus eps times the summand plus eps times the mask form times the product of the
polynomials psi. First round: if the claim is false, the first running claim is the tower's sum for
at most one eps. A variable's round: Tower.round_cnt (rounds_doomed takes off a list of such
rounds). Last round: if what is handed on holds, the last running claim is the tower's value at the
challenges (run_end).

What is asked. Of the summand: a tower with the summand's values at full lists of challenges (Sums).
Of the weights: Weight.OK. Of the written rounds: each but the last draws one element.

Main definitions: OneEl, heardR, errR, Lens, pscRdsY, heardY, pscErrY, pscStepY.

Main theorems: rounds_doomed, psc_sem.

Not claimed. That the program's run on a view is this step's next state. That a summand has a tower:
OnBytes/Slice/KeyLevel.lean shows it of a level's. Nothing on hiding. The sumcheck without a shown
map (no round of Y, no values) is not in this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.KeyPscRun
import OnBytes.Slice.KeyExitStep

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run

/-! ## Written rounds in which elements are sent and one element is drawn -/

/-- The written round d draws one element, read by gOne, and its positions have at most 64 bits. -/
structure OneEl (d : PQ.RD) : Prop where
  inj : Function.Injective (gOne (Fmt.dsOf d.entry d.kind))
  logN : d.entry.logN ≤ 64

/-- A round that draws one element and no position. The element may be one that is never 0. -/
theorem SendsDraws.oneEl {d : PQ.RD} {ns a : ℕ} (h : SendsDraws d ns 1 0 a) : OneEl d :=
  ⟨h.gOne_inj, h.logN⟩

/-- What is heard in a list of written rounds: for each round the elements sent and the first
element drawn (0 if none is drawn). -/
def heardR : (ds : List PQ.RD) → Tr (uW ds) → List (List GE × GE)
  | [], _ => []
  | d :: ds, (m, c, τ) => (ansOf d m, gOne _ (valsOf d c)) :: heardR ds τ

/-- One pair is heard in each round. -/
theorem heardR_length : ∀ (ds : List PQ.RD) (τ : Tr (uW ds)), (heardR ds τ).length = ds.length
  | [], _ => rfl
  | _ :: ds, (_, _, τ) => congrArg (· + 1) (heardR_length ds τ)

/-- The error counts of the rounds of variables whose polynomials have the listed numbers of
coefficients. -/
def errR : List ℕ → (ds : List PQ.RD) → Err (uW ds)
  | _, [] => ()
  | dd, d :: ds => ((dd.headD 0 - 1) * (bsRound .two d.entry d.kind).w, errR dd.tail ds)

/-- In each round one coefficient fewer is sent than the variable's polynomials have. -/
def Lens (ws : List PscF.Weight) (rs : List (List GE × GE)) : Prop :=
  ((ws.zip rs).all fun p => p.2.1.length + 1 == p.1.d) = true

/-- The numbers of sent coefficients fit if the first round's does and the others' do. -/
theorem lens_cons (w : PscF.Weight) (ws : List PscF.Weight) (r : List GE × GE)
    (rs : List (List GE × GE)) : Lens (w :: ws) (r :: rs) ↔ r.1.length + 1 = w.d ∧ Lens ws rs := by
  unfold Lens
  rw [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq]

/-- The tests of work of a list of rounds pass if and only if the first round's does and the
others' do. -/
theorem passT_cons (d : PQ.RD) (ds : List PQ.RD) (m : (wRound d).Msg) (c : (wRound d).Chal)
    (τ : Tr (uW ds)) :
    passT (d :: ds) (m, c, τ) ↔ GChal.pass (b := d.entry.work) c = true ∧ passT ds τ := by
  show (GChal.pass (b := d.entry.work) c && PQ.passSL (ckP .two) ds (PQ.rhoSL (ckP .two) ds τ)) =
    true ↔ _
  rw [Bool.and_eq_true]
  rfl

/-- The rounds of a list of variables are taken off. T is a tower over the weights ws of these
variables followed by further weights. R, the running claim, is not the tower's sum. Then the prover
has lost before the rounds ds, followed by any rounds tl, towards any goal that holds where a test
of work fails or a number of sent coefficients does not fit, provided that it has lost after the
rounds ds whenever the running claim is not the tower's value at the challenges. -/
theorem rounds_doomed : ∀ (ws : List PscF.Weight) (ds : List PQ.RD), ws.length = ds.length →
    (∀ w ∈ ws, w.OK) → (∀ d ∈ ds, OneEl d) → ∀ (rest : List PscF.Weight) (T : List GE → GE),
    PscF.Tower (ws ++ rest) T → ∀ R : GE, R ≠ T [] →
    ∀ (tl : List PQ.RD) (εt : Err (uW tl)) (bad : Tr (uW (ds ++ tl)) → Prop),
    (∀ a b, ¬ passT ds a → bad (joinT ds tl a b)) →
    (∀ a b, ¬ Lens ws (heardR ds a) → bad (joinT ds tl a b)) →
    (∀ a, PscF.claimAfter ws (heardR ds a) R ≠ T ((heardR ds a).map (·.2)) →
      PscF.Tower rest (fun p => T ((heardR ds a).map (·.2) ++ p)) →
      Doomed (uW tl) εt fun b => bad (joinT ds tl a b)) →
    Doomed (uW (ds ++ tl)) (appE ds tl (errR (ws.map (·.d)) ds) εt) bad
  | [], [], _, _, _, _, _, hT, _, hR, _, _, _, _, _, H => H () hR hT
  | w :: ws, d :: ds, hlen, hw, hd, rest, T, hT, R, hR, tl, εt, bad, hp, hl, H => by
    have hw0 := hw w List.mem_cons_self
    have hd0 := hd d List.mem_cons_self
    show Doomed (wRound d :: uW (ds ++ tl))
      ((w.d - 1) * (bsRound .two d.entry d.kind).w, appE ds tl (errR (ws.map (·.d)) ds) εt) bad
    refine draw_cnt d (gOne _) hd0.inj hd0.logN (uW (ds ++ tl)) _ (w.d - 1)
      (fun m x => (ansOf d m).length + 1 = w.d ∧
        PscF.polyAt (w.complete (ansOf d m) R) x = T [x]) (fun m => ?_) bad (fun m c τ hc => ?_)
      fun m c hB => ?_
    · by_cases hs : (ansOf d m).length + 1 = w.d
      · exact le_trans (cnt_mono fun x hx => hx.2) (PscF.Tower.round_cnt hw0 hT hR _ hs)
      · rw [cnt_false fun x hx => hs hx.1]
        exact Nat.zero_le _
    · obtain ⟨a, b, rfl⟩ := exists_joinT ds tl τ
      refine hp (m, c, a) b fun h => ?_
      rw [((passT_cons d ds m c a).1 h).1] at hc
      cases hc
    · by_cases hs : (ansOf d m).length + 1 = w.d
      · refine rounds_doomed ws ds (Nat.succ.inj hlen)
          (fun v hv => hw v (List.mem_cons_of_mem _ hv))
          (fun v hv => hd v (List.mem_cons_of_mem _ hv)) rest
          (fun p => T (gOne _ (valsOf d c) :: p)) (hT.2 _)
          (PscF.polyAt (w.complete (ansOf d m) R) (gOne _ (valsOf d c)))
          (fun h => hB ⟨hs, h⟩) tl εt (fun b => bad (m, c, b)) (fun a b h => ?_) (fun a b h => ?_)
          fun a h1 h2 => H (m, c, a) h1 h2
        · exact hp (m, c, a) b fun h' => h ((passT_cons d ds m c a).1 h').2
        · exact hl (m, c, a) b fun h' => h ((lens_cons w ws _ _).1 h').2
      · refine doomed_of_all _ _ _ fun τ => ?_
        obtain ⟨a, b, rfl⟩ := exists_joinT ds tl τ
        exact hl (m, c, a) b fun h' => hs ((lens_cons w ws _ _).1 h').1

/-! ## The sumcheck with shown maps -/

section
variable (dEps : PQ.RD) (dXs : List PQ.RD) (dY dVals : PQ.RD)

/-- The rounds of a sumcheck with shown maps: the first round, a round for each variable of the
claim, the round of Y, the round of the shown values. -/
abbrev pscRdsY : List PQ.RD := dEps :: (dXs ++ [dY, dVals])

/-- What is heard in the rounds. -/
def heardY (τ : Tr (uW (pscRdsY dEps dXs dY dVals))) : PscF.Heard where
  mu := (ansOf dEps τ.1).headD 0
  eps := gOne _ (valsOf dEps τ.2.1)
  rounds := heardR dXs (fstT dXs [dY, dVals] τ.2.2) ++
    [(ansOf dY (sndT dXs [dY, dVals] τ.2.2).1, gOne _ (valsOf dY (sndT dXs [dY, dVals] τ.2.2).2.1))]
  values := ansOf dVals (sndT dXs [dY, dVals] τ.2.2).2.2.1

/-- The error counts. dd: for each variable of the claim the number of coefficients of a round's
polynomial. dg: the summand's degree. -/
def pscErrY (dd : List ℕ) (dg : ℕ) : Err (uW (pscRdsY dEps dXs dY dVals)) :=
  (1 * (bsRound .two dEps.entry dEps.kind).w,
    appE dXs [dY, dVals] (errR dd dXs)
      (appE [dY] [dVals] (errR [dg + 1] [dY]) ((0, ()) : Err (uW [dVals]))))

variable {X : Type} (cl : X → PscF.Claim) (S : X → PscF.Summand) (fr : X → List Slot)

/-- The written sumcheck with shown maps, as a step. cl, S, fr read the claim, the summand and
the fresh mask entries off the state. The test: the sizes fit. The next state: the state, with what
the run hands on. -/
def pscStepY (dd : List ℕ) (dg : ℕ) : Step X (X × PscF.Out) where
  rds := pscRdsY dEps dXs dY dVals
  err := pscErrY dEps dXs dY dVals dd dg
  ok x τ := PscF.tests (cl x) (S x) (fr x) (heardY dEps dXs dY dVals τ) = true
  nx x τ := (x, PscF.outOf (cl x) (S x) (fr x) (heardY dEps dXs dY dVals τ))

/-- What is asked of the states: the claim's variables are as many as their rounds, their
polynomials have the listed numbers of coefficients, their weights meet Weight.OK; the summand shows
a map and has the degree dg, which is not 0. -/
structure PscSide (dd : List ℕ) (dg : ℕ) (x : X) : Prop where
  len : (cl x).vars.length = dXs.length
  dims : (cl x).vars.map (·.d) = dd
  ok : ∀ w ∈ (cl x).vars, w.OK
  shown : (S x).shown ≠ 0
  deg : (S x).degree = dg
  pos : 1 ≤ dg

end

/-- What is heard, at a transcript given in parts. -/
theorem heardY_joinT (dEps : PQ.RD) (dXs : List PQ.RD) (dY dVals : PQ.RD) (m : (wRound dEps).Msg)
    (c : (wRound dEps).Chal) (a : Tr (uW dXs)) (b : Tr (uW [dY, dVals])) :
    heardY dEps dXs dY dVals (m, c, joinT dXs [dY, dVals] a b) =
      ⟨(ansOf dEps m).headD 0, gOne _ (valsOf dEps c),
        heardR dXs a ++ [(ansOf dY b.1, gOne _ (valsOf dY b.2.1))], ansOf dVals b.2.2.1⟩ := by
  unfold heardY
  simp only [fstT_joinT, sndT_joinT]

/-- Among what run tests: the numbers of sent coefficients fit. -/
theorem tests_lens {c : PscF.Claim} {S : PscF.Summand} {fr : List Slot} {h : PscF.Heard}
    (ht : PscF.tests c S fr h = true) : Lens (PscF.varsOf c S) h.rounds := by
  unfold PscF.tests at ht
  rw [Bool.and_eq_true] at ht
  exact ht.2

/-- The running claim after two lists of rounds. -/
theorem claimAfter_append : ∀ (ws ws' : List PscF.Weight) (rs rs' : List (List GE × GE)) (R : GE),
    ws.length = rs.length → PscF.claimAfter (ws ++ ws') (rs ++ rs') R =
      PscF.claimAfter ws' rs' (PscF.claimAfter ws rs R)
  | [], _, [], _, _, _ => rfl
  | _ :: ws, ws', (_, _) :: rs, rs', _, h =>
    claimAfter_append ws ws' rs rs' _ (Nat.succ.inj h)

/-- The numbers of sent coefficients fit in two lists of rounds if they fit in the joined list. -/
theorem lens_append : ∀ (ws ws' : List PscF.Weight) (rs rs' : List (List GE × GE)),
    ws.length = rs.length → Lens (ws ++ ws') (rs ++ rs') → Lens ws rs ∧ Lens ws' rs'
  | [], _, [], _, _, h => ⟨rfl, h⟩
  | w :: ws, ws', r :: rs, rs', hl, h => by
    have h1 := (lens_cons w (ws ++ ws') r (rs ++ rs')).1 h
    have h2 := lens_append ws ws' rs rs' (Nat.succ.inj hl) h1.2
    exact ⟨(lens_cons w ws r rs).2 ⟨h1.1, h2.1⟩, h2.2⟩

/-- Soundness of the written sumcheck with shown maps. W: the values of the mask entries. V, Kp:
the shown and the kept maps. T x: the summand's tower at the state x. F: a fact on states under
which the sizes fit and T x is the summand's tower. If F holds of the state and the tower's sum plus
the value of the claim's mask form is not the target, then, but for the counted verifier messages,
what the run hands on does not hold. -/
theorem psc_sem (dEps : PQ.RD) (dXs : List PQ.RD) (dY dVals : PQ.RD) {X : Type}
    (cl : X → PscF.Claim) (S : X → PscF.Summand) (fr : X → List Slot) (dd : List ℕ) (dg : ℕ)
    (hE : OneEl dEps) (hX : ∀ d ∈ dXs, OneEl d) (hY : OneEl dY)
    (F : X → Prop) (hside : ∀ x, F x → PscSide dXs cl S dd dg x) (W : PscF.World)
    (V Kp : X → ℕ → List GE → GE) (T : X → List GE → GE)
    (hT' : ∀ x, F x → PscF.Sums W (V x) (Kp x) (cl x) (S x) (fr x) (T x)) :
    (pscStepY dEps dXs dY dVals cl S fr dd dg).Sem
      (fun x => F x → T x [] + W.form (cl x).masks = (cl x).target)
      fun p => p.2.Holds W (V p.1) (Kp p.1) (S p.1).kept := by
  intro x hx0
  obtain ⟨hF, hx⟩ := Classical.not_imp.1 hx0
  have hs := hside x hF
  have hT : PscF.Sums W (V x) (Kp x) (cl x) (S x) (fr x) (T x) := hT' x hF
  have hvars : PscF.varsOf (cl x) (S x) = (cl x).vars ++ [PscF.Weight.atZero (dg + 1)] := by
    unfold PscF.varsOf
    rw [if_neg (by simpa using hs.shown), hs.deg]
  have hwY : (PscF.Weight.atZero (dg + 1)).OK :=
    PscF.equality_ok 0 (dg + 1) (Nat.succ_le_succ hs.pos)
  have hwAll : ∀ w ∈ PscF.varsOf (cl x) (S x), w.OK := by
    intro w hw
    rw [hvars, List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact hs.ok w hw
    · exact hwY
  have htow : ∀ ε, PscF.Tower ((cl x).vars ++ [PscF.Weight.atZero (dg + 1)])
      (PscF.whole W (cl x) (S x) (fr x) (T x) ε) := by
    intro ε
    rw [← hvars]
    exact PscF.Tower.add (PscF.tower_hideT _ _ hwAll) (PscF.Tower.smul ε
      (PscF.Tower.add hT.tower (PscF.Tower.smul _ (PscF.tower_psiT _ hwAll))))
  show Doomed (wRound dEps :: uW (dXs ++ [dY, dVals])) (pscErrY dEps dXs dY dVals dd dg) _
  refine draw_cnt dEps (gOne _) hE.inj hE.logN (uW (dXs ++ [dY, dVals])) _ 1
    (fun m ε => (ansOf dEps m).headD 0 + ε * (cl x).target =
      PscF.whole W (cl x) (S x) (fr x) (T x) ε []) (fun m => ?_) _ (fun m c τ hc hp => ?_)
    fun m c hB => ?_
  · -- at most one eps
    refine cnt_le_one fun ε ε' h1 h2 => ?_
    unfold PscF.whole at h1 h2
    rw [PscF.psiT_nil, mul_one] at h1 h2
    have h3 : (ε - ε') * ((cl x).target - (T x [] + W.form (cl x).masks)) = 0 := by
      linear_combination h1 - h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact sub_eq_zero.1 h4
    · exact absurd (sub_eq_zero.1 h4).symm hx
  · rw [((passT_cons dEps _ m c τ).1 hp).1] at hc
    cases hc
  · -- the rounds of the claim's variables
    rw [← hs.dims]
    refine rounds_doomed (cl x).vars dXs hs.len hs.ok hX [PscF.Weight.atZero (dg + 1)] _
      (htow _) _ hB [dY, dVals] _ _ (fun a b h hp => ?_) (fun a b h _ ht => ?_)
      fun a h1 t1 => ?_
    · exact absurd ((passT_joinT dXs _ a b).1 ((passT_cons dEps _ m c _).1 hp).2).1 h
    · have h2 := tests_lens ht
      rw [heardY_joinT, hvars] at h2
      exact absurd (lens_append _ _ _ _ (hs.len.trans (heardR_length dXs a).symm) h2).1 h
    · -- the round of Y
      refine rounds_doomed [PscF.Weight.atZero (dg + 1)] [dY] rfl
        (fun w hw => by rw [List.mem_singleton.1 hw]; exact hwY)
        (fun d hd => by rw [List.mem_singleton.1 hd]; exact hY) []
        (fun p => PscF.whole W (cl x) (S x) (fr x) (T x) (gOne _ (valsOf dEps c))
          ((heardR dXs a).map (·.2) ++ p)) t1 _ (by
            beta_reduce
            rw [List.append_nil]
            exact h1) [dVals] ((0, ()) : Err (uW [dVals])) _
        (fun y v h hp => ?_) (fun y v h _ ht => ?_) fun y h2 _ => ?_
      · exact absurd ((passT_joinT [dY] [dVals] y v).1
          ((passT_joinT dXs _ a _).1 ((passT_cons dEps _ m c _).1 hp).2).2).1 h
      · obtain ⟨mY, cY, ⟨⟩⟩ := y
        have h3 := tests_lens ht
        rw [heardY_joinT, hvars] at h3
        exact absurd (lens_append _ _ _ _ (hs.len.trans (heardR_length dXs a).symm) h3).2 h
      · -- the round of the shown values
        obtain ⟨mY, cY, ⟨⟩⟩ := y
        refine doomed_of_all _ _ _ fun v _ ht ho => h2 ?_
        have h3 := PscF.run_end W (V x) (Kp x) (cl x) (S x) (fr x) _ ht hwAll (T x) hT ho
        rw [heardY_joinT, hvars] at h3
        simp only [] at h3
        rw [claimAfter_append _ _ _ _ _ (hs.len.trans (heardR_length dXs a).symm),
          List.map_append] at h3
        exact h3

end OnBytes.Slice
