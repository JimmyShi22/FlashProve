-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/FallAtt.lean: `Gathers` AND THE COUNT OF
Johnson/Desc/K8/Honest/FallCount.lean AT AN ATTENTION SEGMENT's BATCHING; AND, AS A CHECK OF THE
GENERAL LEMMA, `Gathers` AT A FEED-FORWARD SEGMENT ONCE MORE. Statements and proofs. No prover.
Lemmas; none of the library's goals. NOTHING IS CLAIMED ON COMPLETENESS, SOUNDNESS OR HIDING.

By the general lemma `gathers_of_plain` (Johnson/Desc/K8/Honest/GathersPlain.lean): each run of
claims of the segment, but for "K8.equations", is free of the batching element.
  **`gathers_layers_plain`**   a feed-forward segment: the statement of `gathers_layers_any`
      (Johnson/Desc/K8/Honest/FallLayersAny.lean), from the general lemma: its third stretch is the
      run "back"
  `inAt_re`, `inOf_re`, `pad_re`, `keysOfK_re`, `readersOfK_re`   all that attention's own runs, its
      keys and its readers read of a state goes through one function, which reads of the ledger what
      is shown under slots and one array's number of columns
  `plain_first`, `plain_keys`, `plain_second`   attention's own three runs
  **`gathers_att`**   from the ties (`AttTies`; the two at "objects"; tJ: the run at (2, "join")
      stands under the lookup's own at attention's keys; tP: the run at (1, "planes") under the
      lookup's own at attention's readers, at some lm) and the order: at every state that holds data
      tl and a list of tables funs: `Gathers`, at SOME numbers and coefficients
  `fall_few_any`, `funs_of_yes`   the count from `Gathers` at whatever the state holds
  **`fall_few_att`**   so the count at an attention segment, in the form of `fall_few_layers`
c: attention's numbers; at the proof file's description c is parCOf of the segment's plan.
Limits: the ties are premises. That a reached state's data pass `unitsLaid`, and the seat, are not
said here.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.GathersPlain
import Johnson.Desc.K8.Honest.FallFew
import Johnson.Desc.First.Link.Law.PayAttention

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.Att
open OnBytes.Tie.Pv.Tail.Port (topOf)

/-! ## A feed-forward segment, from the general lemma -/

/-- **`Gathers` at a feed-forward segment**, from the general lemma: the statement of
`gathers_layers_any`. -/
theorem gathers_layers_plain (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat)
    (p : K9.Where) (s : S) (tl : HTailF2) (funs : Array HFun)
    (ties : LinkJoin.LayersTies L p4 nU)
    (tC : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run K9.objectsDigits)
    (hord : L.order = orderOf .layers) (ht : s.tl? = some tl) (hf : s.funs? = some funs) :
    ∃ (nf nb : Nat) (a : Nat → Nat → Nat → Nat → Cb.Gl.E),
      Gathers p (claimsInBy L.each L.hear L.order) s tl funs nf nb a := by
  refine gathers_of_plain L p 4
    [(1, "objects"), (1, "guests"), (2, "front"), (6, "objects"), (6, "guests")] [(2, "back")]
    (by rw [hord]; rfl) ?_ ?_ ties.tEq s tl funs ht hf
  · intro o ho run hat
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, tC run hat, plain_objectsCalls⟩
    · exact ⟨_, ties.tGuests 1 (by simp) run hat, plain_idle⟩
    · obtain ⟨r, l, u⟩ := ties.tFront run hat
      exact ⟨r, u, plain_front p4 r l⟩
    · exact ⟨_, tD run hat, plain_objectsDigits⟩
    · exact ⟨_, ties.tGuests 6 (by simp) run hat, plain_idle⟩
  · intro o ho run hat
    obtain rfl : o = (2, "back") := List.mem_singleton.1 ho
    obtain ⟨r, l, u⟩ := ties.tBack run hat
    exact ⟨r, u, behind_back p4 r l⟩

/-! ## What attention's runs read of a state -/

theorem att_reChi (θ : E) (t : S) (a : AttOwn) (h : t.here = .att a) :
    (reChi θ t).here = .att { a with F := reChiF θ a.F } := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := t
  obtain rfl : here = .att a := h
  rfl

theorem att_back (θ : E) (t : S) (b : AttOwn) (h : (reChi θ t).here = .att b) :
    ∃ a, t.here = .att a := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := t
  cases here with
  | att x => exact ⟨x, rfl⟩
  | lay x => exact absurd h (by simp [reChi, S.fork?, S.putFork])
  | head x => by_cases ho : x.opened = true <;> simp [reChi, S.fork?, S.putFork, ho] at h
  | between => exact absurd h (by simp [reChi, S.fork?])
  | fin x => exact absurd h (by simp [reChi, S.fork?])
  | mem x => exact absurd h (by simp [reChi, S.fork?])

theorem inAt_re (c : P.ParC) (g : Forest.Heard) (h : P.Heard) (θ : E) (F : Fork) :
    K5Law.inAt c g h (reChiF θ F) = K5Law.inAt c g h F := by
  unfold K5Law.inAt P.ptsFrom P.leftP P.left P.leftKey
  simp only [shown_re]
  rfl

theorem inOf_none (c : P.ParC) (t : S) (h : ∀ a, t.here ≠ .att a) :
    P.inOf (P.seatCO c) c t = none := by
  cases e : P.inOf (P.seatCO c) c t with
  | none => rfl
  | some x =>
    obtain ⟨a, ha⟩ := K5Law.att_of_inOf e
    exact absurd ha (h a)

theorem inOf_re (c : P.ParC) (θ : E) (t : S) :
    P.inOf (P.seatCO c) c (reChi θ t) = P.inOf (P.seatCO c) c t := by
  by_cases hatt : ∃ a, t.here = .att a
  · obtain ⟨a, ha⟩ := hatt
    rw [K5Law.inOf_isAt (att_reChi θ t a ha), K5Law.inOf_isAt ha]
    show (a.g.bind fun g => a.heard5.bind fun h => K5Law.inAt c g h (reChiF θ a.F)) = _
    simp only [inAt_re]
  · rw [inOf_none c t fun a ha => hatt ⟨a, ha⟩,
      inOf_none c (reChi θ t) fun b hb => hatt (att_back θ t b hb)]

theorem pad_putFork (c : P.ParC) (s : S) (G : Fork) :
    (P.seatCO c).pad (s.putFork G) = (P.seatCO c).pad s := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay x => rfl
  | att x => rfl
  | head x => by_cases ho : x.opened = true <;> simp [P.seatCO, S.putFork, ho]
  | between => rfl
  | fin x => rfl
  | mem x => rfl

theorem pad_re (c : P.ParC) (θ : E) (t : S) :
    (P.seatCO c).pad (reChi θ t) = (P.seatCO c).pad t :=
  reChi_read (P.seatCO c).pad (pad_putFork c) θ t

theorem keysOfK_re (c : P.ParC) (θ : E) (t : S) :
    P.keysOfK (P.seatCO c) c (reChi θ t) = P.keysOfK (P.seatCO c) c t := by
  unfold P.keysOfK
  rw [inOf_re, pad_re]

theorem readersOfK_re (c : P.ParC) (θ : E) (t : S) :
    P.readersOfK (P.seatCO c) c (reChi θ t) = P.readersOfK (P.seatCO c) c t := by
  unfold P.readersOfK
  rw [inOf_re]

/-! ## Attention's own three runs -/

theorem plain_first (c : P.ParC) : PlainRun (K5Law.runFirst c) :=
  plain_still "K5.first" (P.firstK (P.seatCO c) c)
    (fun t z h => by
      unfold P.firstK at h
      obtain ⟨⟨i, K⟩, -, h⟩ := Option.bind_eq_some_iff.1 h
      dsimp only at h
      obtain ⟨r, -, h⟩ := Option.bind_eq_some_iff.1 h
      obtain rfl := Option.some.inj h
      rfl)
    (fun θ t => by
      unfold P.firstK
      rw [inOf_re]
      cases P.inOf (P.seatCO c) c t with
      | none => rfl
      | some x =>
        obtain ⟨i, K⟩ := x
        simp only [Option.bind_eq_bind, Option.bind_some]
        cases P.Runs.firstRun i K <;> rfl)

theorem plain_keys (c : P.ParC) : PlainRun (K5Law.runKeys c) :=
  plain_still "K5.keys" (P.keysK (P.seatCO c) c)
    (fun t z h => by
      unfold P.keysK at h
      obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 h
      rfl)
    (fun θ t => by
      unfold P.keysK
      rw [keysOfK_re]
      cases P.keysOfK (P.seatCO c) c t <;> rfl)

theorem plain_second (c : P.ParC) : PlainRun (K5Law.runSecond c) :=
  plain_still "K5.second" (P.secondK (P.seatCO c) c)
    (fun t z h => by
      unfold P.secondK at h
      obtain ⟨⟨i, K⟩, -, h⟩ := Option.bind_eq_some_iff.1 h
      dsimp only at h
      obtain ⟨r, -, h⟩ := Option.bind_eq_some_iff.1 h
      obtain rfl := Option.some.inj h
      rfl)
    (fun θ t => by
      unfold P.secondK
      rw [inOf_re]
      cases P.inOf (P.seatCO c) c t with
      | none => rfl
      | some x =>
        obtain ⟨i, K⟩ := x
        simp only [Option.bind_eq_bind, Option.bind_some]
        cases P.Runs.secondRun i K <;> rfl)

/-! ## The segment -/

/-- The entries of an attention segment's order in front of "K8.equations". -/
def attPre : List (Nat × String) :=
  [(1, "objects"), (1, "guests"), (2, "first"), (2, "keys"), (2, "join"), (2, "second"),
    (1, "planes"), (6, "objects"), (6, "guests")]

theorem att_pre (L : Link S Claim) (c : P.ParC) (nU : Array Nat) (ties : LinkJoin.AttTies L c nU)
    (tC : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run K9.objectsDigits)
    (tJ : ∀ run, LinkJoin.At L (2, "join") run →
      LinkJoin.Under run (K9.joinCalls (P.keysOfK (P.seatCO c) c)))
    (tP : ∀ run, LinkJoin.At L (1, "planes") run →
      ∃ lm, LinkJoin.Under run (K9.planesCalls lm (P.readersOfK (P.seatCO c) c))) :
    PreOk L attPre := by
  intro o ho run hat
  simp only [attPre, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, tC run hat, plain_objectsCalls⟩
  · exact ⟨_, ties.tGuests 1 (by simp) run hat, plain_idle⟩
  · exact ⟨_, ties.tFirst run hat, plain_first c⟩
  · exact ⟨_, ties.tKeys run hat, plain_keys c⟩
  · exact ⟨_, tJ run hat, plain_join _ (keysOfK_re c)⟩
  · exact ⟨_, ties.tSecond run hat, plain_second c⟩
  · obtain ⟨lm, u⟩ := tP run hat
    exact ⟨_, u, plain_planes lm _ (readersOfK_re c)⟩
  · exact ⟨_, tD run hat, plain_objectsDigits⟩
  · exact ⟨_, ties.tGuests 6 (by simp) run hat, plain_idle⟩

theorem post_nil (L : Link S Claim) : PostOk L [] := fun _ ho => nomatch ho

/-- **`Gathers` at an attention segment.** -/
theorem gathers_att (L : Link S Claim) (c : P.ParC) (nU : Array Nat) (p : K9.Where) (s : S)
    (tl : HTailF2) (funs : Array HFun) (ties : LinkJoin.AttTies L c nU)
    (tC : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run K9.objectsDigits)
    (tJ : ∀ run, LinkJoin.At L (2, "join") run →
      LinkJoin.Under run (K9.joinCalls (P.keysOfK (P.seatCO c) c)))
    (tP : ∀ run, LinkJoin.At L (1, "planes") run →
      ∃ lm, LinkJoin.Under run (K9.planesCalls lm (P.readersOfK (P.seatCO c) c)))
    (hord : L.order = orderOf .attention) (ht : s.tl? = some tl) (hf : s.funs? = some funs) :
    ∃ (nf nb : Nat) (a : Nat → Nat → Nat → Nat → Cb.Gl.E),
      Gathers p (claimsInBy L.each L.hear L.order) s tl funs nf nb a := by
  exact gathers_of_plain L p 4 attPre [] (by rw [hord]; rfl) (att_pre L c nU ties tC tD tJ tP)
    (post_nil L) ties.tEq s tl funs ht hf

/-- The count from `Gathers` at whatever the state holds. batch: a decision each of whose yeses at s
is a yes of the batching block at g, with the same return. -/
theorem fall_few_any (p : K9.Where) (g : S → Except String (List Claim × S))
    (batch : S → List Fmt.RoundView → Except String S) (nU : Array Nat) (s : S) (tU d : Nat)
    (hG : ∀ tl funs, s.tl? = some tl → s.funs? = some funs →
      ∃ (nf nb : Nat) (a : Nat → Nat → Nat → Nat → Cb.Gl.E), Gathers p g s tl funs nf nb a)
    (hfuns : ∀ dr t e cls, drawnAt p s dr = .ok t → g t = .ok (cls, e) → s.funs?.isSome = true)
    (hb : ∀ rs t, batch s rs = .ok t → (K9.batch K9.atS p g).decide s rs [] = .ok t)
    (hU : ∀ tl, s.tl? = some tl → unitsLaid nU tl tU = true)
    (hd : ∀ tl F funs, s.tl? = some tl → s.fork? = some F → s.funs? = some funs →
      F.planClaimsF + topOf tl funs ≤ d + 1) :
    Prob.cnt (fun x : Cb.Gl.E => askBehind batch (zeroUnitAt nU) s [chiAt x] = true) ≤
      nU.getD 2 0 * d := by
  by_cases hne : ∃ x : Cb.Gl.E, askBehind batch (zeroUnitAt nU) s [chiAt x] = true
  · obtain ⟨x, hx⟩ := hne
    unfold askBehind at hx
    simp only [List.map_cons, List.map_nil] at hx
    cases hbt : batch s [⟨[], chiAt x⟩] with
    | error e =>
      rw [hbt] at hx
      exact absurd hx (by simp)
    | ok t' =>
      obtain ⟨t, e, cls, y, G, hdr, hg, -, -, -⟩ := batch_ok p g s t' (chiAt x) (hb _ _ hbt)
      obtain ⟨a0, -, -, ha0, -, -, -⟩ := drawnAt_ok p s t (chiAt x) hdr
      have hF : s.fork? = some a0.F := K9.get_fork s a0 ha0
      obtain ⟨funs, hf⟩ := Option.isSome_iff_exists.1 (hfuns _ _ _ _ hdr hg)
      obtain ⟨tl, ht⟩ : ∃ tl, s.tl? = some tl := by
        cases h : s.tl? with
        | some tl => exact ⟨tl, rfl⟩
        | none =>
          exfalso
          simp [K9.atS, h] at ha0
      obtain ⟨nf, nb, a, hGa⟩ := hG tl funs ht hf
      exact fall_few p g batch nU s tl a0.F funs tU nf nb d a hb
        ((tlFork_iff s tl a0.F).2 ⟨ht, hF⟩) (hU _ ht) hGa (hd _ _ _ ht hF hf)
  · rw [Prob.cnt_false fun x hx => hne ⟨x, hx⟩]
    exact Nat.zero_le _

/-- A yes of a function of claims whose order has "K8.equations": the state in front of the draw
holds a
list of tables. -/
theorem funs_of_yes (L : Link S Claim) (p : K9.Where) (i : Nat) (pre post : List (Nat × String))
    (hord : L.order = pre ++ (i, "K8.equations") :: post) (Hpre : PreOk L pre)
    (Hpost : PostOk L post)
    (tEq : ∀ run, LinkJoin.At L (i, "K8.equations") run → LinkJoin.Under run K9L.k8Run.2) (s : S)
    (dr : Fmt.Drawn) (t e : S) (cls : List Claim) (hdr : drawnAt p s dr = .ok t)
    (hg : claimsInBy L.each L.hear L.order t = .ok (cls, e)) : s.funs?.isSome = true := by
  obtain ⟨fr, k8, bk, e₁, e₂, F, F₂, tl₁, tl', funs₁, W⟩ :=
    walk_one L i pre post hord Hpost tEq t e cls hg
  obtain ⟨c, -, -, -, c4, -⟩ := pre_one L pre Hpre _ _ W.a1
  obtain ⟨-, -, xf⟩ := drawnAt_part p s t dr hdr
  have h := W.a4
  rw [c4, xf] at h
  rw [h]
  rfl

/-- **The count at an attention segment's batching.** -/
theorem fall_few_att (L : Link S Claim) (c : P.ParC) (nU : Array Nat) (p : K9.Where)
    (batch : S → List Fmt.RoundView → Except String S) (s : S) (tU d : Nat)
    (ties : LinkJoin.AttTies L c nU)
    (tC : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run K9.objectsDigits)
    (tJ : ∀ run, LinkJoin.At L (2, "join") run →
      LinkJoin.Under run (K9.joinCalls (P.keysOfK (P.seatCO c) c)))
    (tP : ∀ run, LinkJoin.At L (1, "planes") run →
      ∃ lm, LinkJoin.Under run (K9.planesCalls lm (P.readersOfK (P.seatCO c) c)))
    (hord : L.order = orderOf .attention)
    (hb : ∀ rs t, batch s rs = .ok t →
      (K9.batch K9.atS p (claimsInBy L.each L.hear L.order)).decide s rs [] = .ok t)
    (hU : ∀ tl, s.tl? = some tl → unitsLaid nU tl tU = true)
    (hd : ∀ tl F funs, s.tl? = some tl → s.fork? = some F → s.funs? = some funs →
      F.planClaimsF + topOf tl funs ≤ d + 1) :
    Prob.cnt (fun x : Cb.Gl.E => askBehind batch (zeroUnitAt nU) s [chiAt x] = true) ≤
      nU.getD 2 0 * d :=
  fall_few_any p _ batch nU s tU d
    (fun tl funs ht hf => gathers_att L c nU p s tl funs ties tC tD tJ tP hord ht hf)
    (fun dr t e cls hdr hg => funs_of_yes L p 4 attPre [] (by rw [hord]; rfl)
      (att_pre L c nU ties tC tD tJ tP) (post_nil L) ties.tEq s dr t e cls hdr hg)
    hb hU hd

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.fall_few_att
#print axioms VerifiableInference.Desc.First.K8.Honest.gathers_layers_plain
#print axioms VerifiableInference.Desc.First.K8.Honest.inOf_re
#print axioms VerifiableInference.Desc.First.K8.Honest.plain_first
#print axioms VerifiableInference.Desc.First.K8.Honest.plain_keys
#print axioms VerifiableInference.Desc.First.K8.Honest.plain_second
#print axioms VerifiableInference.Desc.First.K8.Honest.gathers_att
#print axioms VerifiableInference.Desc.First.K8.Honest.fall_few_any
#print axioms VerifiableInference.Desc.First.K8.Honest.funs_of_yes
