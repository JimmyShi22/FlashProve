-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/PlanesFront.lean.
WHAT IT IS NOT. NO ITEM BEHIND THE SUB-PROTOCOL IS SHOWN HERE: these are the premises of a law on
the item formsT 24 3 "planes", paid at the first chain's thread; the law itself is not called. EVERY
STATEMENT IS CONDITIONAL ON THE LIBRARY's HYPOTHESIS P5J.AtMgA; the third, fourth and fifth on "the
thread holds at border 341", which is shown of no run. THAT THE ITEM worth 24 3 "planes" HOLDS IN
FRONT IS READ OFF THE THREAD's SENTENCE: it is owed by the row in front (the lookup on the calls):
nothing here pays it. (Of the hypothesis the library has a member under four premises on the three
public files: P5J.head_exists_at_name, Johnson/P5J/HeadExistsAtName.lean; nothing here calls that.)
The full size, the format's second hash function, border 341 and segment 24 alone. Nothing on soundness, on
completeness or on what a proof hides.
WHAT IT IS. The sub-protocol "the output head's own rounds", at the first chain's thread at the
library's own letters (lettersHead, Honest/Thread/FirstHead.lean):
  plane_at_head          three public facts: the place of the lookup on the calls has the caller's
                         shape; the caller's packing is the head's; an inequality on the plan's
                         numbers
  planes_open_341        the item worth 24 3 "planes" is open at border 341: by the kernel, on the
                         library's table of rows
  k6_planes_worth_front  where the thread holds at 341: the composed meaning's field worth 24 3
                         "planes" at the state in front, at every continuation of the challenges and
                         AT EVERY LIST OF STRINGS (the field does not read them)
  k6_planes_in_behind    behind the member's step the table's test on the forms accepts at the run
                         (2, "planes")
  k6_planesDue_at_head   behind the member's step: the bare sub-protocol's decision at the rounds
                         without the sealed digest, K6On in front, and K6PlanesDue
                         (Johnson/Desc/K6/Honest/Law/PlanesDue.lean)
  k6_means_planes        what the item formsT 24 3 "planes" means at these letters follows from the
                         composed meaning's field: by unfolding
WHO PAYS WHAT. plane_at_head: the library's link24_at_head, paid_at_const, placeAt_headAt,
calls_place, place_head, sizes_five, fs_in_scope, plan_in_scope, as its own law has them
(Johnson/Desc/Kinds/Law/K6LawAtMgAll.lean). k6_planes_worth_front: k6_means_worth
(Honest/K6/Law/MeansIn.lean) and the library's mgAll_worth_head_planes
(Johnson/Desc/Sound/MgAllAt.lean). k6_planes_in_behind: k6_form_behind
(Honest/K6/Law/FormBehind.lean: the promise behind the step, at every letter Kp), as that file does
at the four other runs. k6_planesDue_at_head: planesDue_of_step at dueFront_at_head, duePub_at_head
(Honest/K6/Law/DueAtHead.lean, Johnson/Desc/K6/Honest/Law/DueMade.lean), meets_at_head
(Honest/K6/Law/LettersAtHead.lean), strict_of_stepped (the same DueAtHead.lean),
headFrontItems_of_thr (Honest/K6/Law/FrontAt.lean), k6_member_at_mg
(Johnson/Desc/Kinds/Law/K6WayUpAtSeat.lean), the library's paid_at_const, ns_at_const,
six_of_link_at_head, callsC_at_head_all, calls_of_C. TYPED AFTER: plane_at_head's first two steps
are those of calls_at_head (Honest/K6/Law/LettersAtHead.lean), its last two the library's
(Johnson/Desc/Kinds/Law/K6LawAtMgAll.lean, where they stand inside a proof); k6_planes_in_behind
goes as forms_of_parts and k6_forms_behind (Honest/K6/Law/FormsBehind.lean); k6_planesDue_at_head's
first lines and its nsEq as due_at_head (Honest/K6/Law/DueAtHead.lean) and dueFront_of_items
(Johnson/Desc/K6/Honest/Law/DueMade.lean); k6_means_planes as k6_means_at
(Honest/K6/Law/Share.lean), which stands at piece 4 alone.
OF THE FOLDER Johnson/Goal/ it imports no module by name.
It imports, beside library files, those named above under Honest/ and what they import.

-/
import Johnson.Desc.K6.Honest.Law.PlanesDue
import Johnson.Desc.ProofFile.Honest.K6.Law.ShareAtHead
import Johnson.Desc.ProofFile.Honest.K6.Law.FormBehind
import Johnson.Desc.ProofFile.Honest.K6.Law.LettersAtHead
import Johnson.Desc.ProofFile.Honest.Thread.FirstRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open VerifiableInference.Desc (Chain Link Place Strs noDigest)
open VerifiableInference.Desc.First (Item S start pubOfItems)
open VerifiableInference.Desc.Sound (MsgT mgAll mgBase mgMore openQ pubQ)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS mgAtAll At.X)
open ProofFile.Honest (Thr ProverCoinCounts Coins Local Mid Env Prover drawsFit fwdOpen FirstRows.rows)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.Small (PartsAt partsAt_of_formP)
open ProofFile.Honest.K6 (k6_form_behind headFrontItems_of_thr strict_of_stepped dueFront_at_head)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THREE PUBLIC FACTS ON THE LOOKUP ON THE CALLS.** CONDITIONAL on the one hypothesis. -/
theorem plane_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (∀ p, First.Look.placeAt (At.X Zp) 24 false = some p → p.shape = some x.fs) ∧
      x.lm = (At.X Zp).hS.lmbH ∧
      x.fs.NC * 2 ^ (x.fs.kT + 5 - (At.X Zp).hS.lmbH) ≤
        ((At.X Zp).H.tl.mats.getD ((At.X Zp).hS.NHf + 1 + 1) {}).k *
          (((At.X Zp).H.tl.mats.getD ((At.X Zp).hS.NHf + 1 + 1) {}).m /
            2 ^ (At.X Zp).hS.lmbH) := by
  obtain ⟨Lk, hlk⟩ := P4.link24_at_head h
  have A := paid_at_const h Lk hlk
  have hsh : (First.Look.P.ofPlace (OnBytes.Params.settingOf (At.X Zp).P.frame) false x).shape =
      some x.fs := by
    have hx := A.place
    unfold headAt at hx
    obtain ⟨x', -, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨h', hh, hx⟩ := Option.map_eq_some_iff.1 hx
    subst hx
    exact hh
  have hpl3 : First.Look.placeAt (At.X Zp) 24 false =
      some (First.Look.P.ofPlace (OnBytes.Params.settingOf (At.X Zp).P.frame) false x) := by
    -- placeAt_headAt stands under three instance variables of its file, which its statement does
    -- not read: any will do; so below, at place_head
    letI := (parOf (At.X Zp).hS 0).sizes
    letI := (parOf (At.X Zp).hS 0).policy
    letI : Request := ⟨fun _ => 0, 0, 0⟩
    have e5 := VerifiableInference.OnPublicFiles.placeAt_headAt A.place
    rw [A.seg] at e5
    exact e5
  obtain ⟨pc, ec, sc, _, _⟩ := InScope.calls_place h.scope h.pubOne
  obtain rfl := Option.some.inj (hpl3.symm.trans ec)
  have hfs : (At.X Zp).HLy.fs = x.fs := Option.some.inj (sc.symm.trans hsh)
  refine ⟨fun p hp => ?_, ?_, ?_⟩
  · rw [← Option.some.inj (hpl3.symm.trans hp)]
    exact hsh
  · letI := (parOf (At.X Zp).hS 0).sizes
    letI := (parOf (At.X Zp).hS 0).policy
    letI : Request := ⟨fun _ => 0, 0, 0⟩
    exact (First.Look.place_head h.pubOne
      (VerifiableInference.OnPublicFiles.placeAt_headAt A.place)).2.1
  · obtain ⟨z1, _, _, z4, _, _, _, _⟩ := InScope.sizes_five h.scope h.reads h.pubOne
    rw [← hfs, (InScope.fs_in_scope h.scope h.reads h.pubOne).NC,
      (InScope.fs_in_scope h.scope h.reads h.pubOne).kT, z4, z1,
      (InScope.plan_in_scope h.scope h.reads h.pubOne).mats]
    decide

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE ITEM worth 24 3 "planes" IS OPEN AT BORDER 341.** By the kernel, on the library's table of
rows read forward. CONDITIONAL: the hypothesis h, for the thread's sake alone. -/
theorem planes_open_341 :
    Item.worth 24 3 "planes" ∈
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened 341 := by
  have e : Item.worth 24 3 "planes" ∈ fwdOpen (start P5J.At.links)
      (FirstRows.rows P5J.At.links P5J.At.ps) 341 := by
    decide +kernel
  exact e

/-- **THE COMPOSED MEANING's FIELD worth 24 3 "planes" IN FRONT**, at every continuation ds of the
challenges heard and at every list y of strings. CONDITIONAL: the hypothesis h; hT: the thread holds
at border 341: the item is one of those that it holds open there. -/
theorem k6_planes_worth_front {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 341 k s m E)
    (ds : List Fmt.Drawn) (y : Strs) :
    (mgAll (dofAtHead h Q carryX m.st.input) mgBase).worth 24 3 "planes"
      (((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.seat k m s).1, s) y
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k m.st.input
        (m.st.heard ++ ds)) := by
  have hA := hT
  unfold Thr at hA
  obtain ⟨-, -, -, hI0, -, -, -⟩ := hA
  have h0 := hI0 ds _ (planes_open_341 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
  have h1 := k6_means_worth (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    (Dof := dofAtHead h Q carryX) (Mg₀ := mgBase) (fun _ => rfl) 24 3 "planes" _ _ _ _ h0
  obtain ⟨Lk, hlk⟩ := P4.link24_at_head h
  have A := paid_at_const h Lk hlk
  rw [← A.seg, Sound.mgAll_worth_head_planes _ mgBase A.place] at h1 ⊢
  exact h1

/-- **BEHIND THE MEMBER's STEP THE TABLE's TEST ON THE FORMS ACCEPTS AT THE RUN (2, "planes").** At
every letter Kp. CONDITIONAL: the hypothesis h; the thread holds at 341; the list of challenges
fits; the member's step. -/
theorem k6_planes_in_behind :
    ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[341]? = some blk →
      ∀ k s m E ds y cl s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 341 k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cl
        s' →
      K9.formsInT (h.𝔇.Rd 24) (h.𝔇.N.sent 24 0) 2 "planes" s' = true := by
  intro blk hblk k s m E ds y cl s' hT hd hS
  obtain ⟨hf, hP⟩ := k6_form_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w blk hblk k s m E ds y
    cl s' hT hd hS
  have hf' : s'.failed.isNone = true := hf
  have Pa : PartsAt (P5J.At.N Zp cF) (mgAtAll h) P5J.At.links P5J.At.ps (341 + 1)
      (y.2.st.input.x.pub, s') :=
    partsAt_of_formP (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) (341 + 1)
      (y.2.st.input.x.pub, s') hP (Option.isNone_iff_eq_none.1 hf')
  obtain ⟨Lk, hl, -⟩ := P4.six_at_head h
  have Pd := paid_at_const h Lk hl
  obtain ⟨-, rp, -, -, -⟩ := runs_at_head h.𝔇 Pd.sorts
  have hm : (mgAtAll h).more = mgMore := Sound.mgAll_more_base h.𝔇
  have h342 : pubQ mgMore P5J.At.links P5J.At.ps (341 + 1) ++
      pubOfItems (openQ P5J.At.links P5J.At.ps (341 + 1)) = _ := open342
  have hpl := Pa.pub (.formsInT 24 3 "planes") (by rw [hm, h342]; simp)
  have hp : (mgAtAll h).pub = _ := Sound.mgAll_pub h.𝔇 mgBase
  rw [hp, First.pubAll_formsInT] at hpl
  have ep : h.𝔇.pubD.runs 24 3 "planes" = [(2, "planes")] := rp
  rw [ep] at hpl
  simp only [List.all_cons, List.all_nil, Bool.and_true] at hpl
  exact hpl

/-- **WHAT THE LAW ON "PLANES" ASKS OF THE TWO STATES, AT THE THREAD**, at every Lk that is the
first chain's link 24 and at the composed meaning's data at every input v. CONDITIONAL: the
hypothesis h; the thread holds at 341; the list of challenges fits; the member's step. The bare
sub-protocol's decision stands at the rounds without the sealed digest: so the step shows them. -/
theorem k6_planesDue_at_head (Lk : Link S ProofFile.Cl) (hlk : cF.links[24]? = some Lk)
    (v : Local W₀ Rc ProofFile.Inst Tr) :
    ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[341]? = some blk →
      ∀ k s m E ds y cl s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 341 k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cl
        s' →
      ∃ gs, (Sound.below (blockAt (At.X Zp).hS (readsOf (At.X Zp)) (workOf (At.X Zp)) 24)).decide s
          ((ProofFile.Honest.roundsOf y.1).map noDigest) gs = .ok s' ∧
        K6On (At.X Zp) s ∧
        ∃ aK cU, K6PlanesDue (dofAtHead h Q carryX v) x (K9.statesOfLink Lk) s s' aK cU := by
  intro blk hblk k s m E ds y cl s' hT hd hS
  obtain ⟨b, hb, M⟩ := P4.k6_member_at_mg h.toAtMg
  have hblk' : cF.blocksInOrder[341]? = some blk := hblk
  obtain rfl : b = blk := Option.some.inj (hb.symm.trans hblk')
  have hc : cl = [] := by
    have h3 := ((VerifiableInference.Desc.step_iff _ b s s' _ cl _).1 hS.2).2.2
    rw [M.want] at h3
    exact List.eq_nil_of_length_eq_zero h3
  have hstr := strict_of_stepped _ hd hS hc
  have A := paid_at_const h Lk hlk
  obtain ⟨-, R⟩ := headFrontItems_of_thr
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) h.𝔇 rfl rfl rfl rfl hT
  have nsEq : ∀ F, s.fork? = some F → F.ns = (At.X Zp).H.ns := fun G hG => by
    have h1 := R.freeAbove
    rw [ns_at_const h] at h1
    have h2 : First.freeAboveB (At.X Zp).H.ns s = true := h1
    unfold First.freeAboveB at h2
    rw [hG] at h2
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h2
    exact h2.2
  obtain ⟨hpl, -, hcols⟩ := plane_at_head h
  exact planesDue_of_step (dofAtHead h Q carryX v) M
    (P5J.flat_ok h.toAtMg b (List.mem_of_getElem? hb)) hstr
    (dueFront_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT) Lk
    (AtFold.duePub_at_head h Lk hlk _ (P5J.laid_at_head h.toAtMg)) K9.smallReader A.readers
    (P4.six_of_link_at_head h hlk).2.2.1 nsEq (meets_at_head h _ _)
    (AtFold.calls_of_C (callsC_at_head_all h) (colsB (At.X Zp)) (fun a _ hc' => by
      have e : a = (At.X Zp).hS.NHf + 2 := hc'
      omega))
    (fun μ r c hr hc' _ => h.plan.hN 24 μ r c hr hc') hpl hcols

/-- What the item formsT 24 3 "planes" means at these letters follows from the composed meaning's
field: by unfolding. CONDITIONAL: the hypothesis h, for the thread's sake alone. It shows no item
true. -/
theorem k6_means_planes :
    ∀ v a y u, (mgAll (dofAtHead h Q carryX v) mgBase).formsT 24 3 "planes" (a.1, a.2) y u →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.means v
        (Item.formsT 24 3 "planes") a y u := by
  intro v a y u hu
  have hMg : ∀ v, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).Mg v =
      mgAll (dofAtHead h Q carryX v) mgBase := fun _ => rfl
  show Item.holds (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).N
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mg v) (Item.formsT 24 3 "planes") a y
    u
  unfold ProofFile.Honest.FirstThread.Letters.mg
  rw [hMg v]
  exact hu

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.plane_at_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.planes_open_341
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_planes_worth_front
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_planes_in_behind
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_planesDue_at_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_means_planes
