-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/KxAtFront.lean: THE LOOKUPS' PROMISE ON WHAT IS FIXED (`K3Ok`,
Johnson/Top/H/Keep/RunsPlain.lean), AT WHAT IS FIXED AT A STATE, FROM THEIR PROMISE ON THE STATE
ITSELF (`K3LeftOn`, Johnson/Top/H/K3LeftStatement.lean); that promise at the digits' seat at every
state reached in front of a batching; so `kxAll` (SortLetters.lean) there. Theorems: joins of other
files' lemmas.
Why. The law of a link is asked at Ok := the sort's named Ok AND `kxAll lmC jC lmD jD` (OkOne.lean's
head says why). So `kxAll` of what is fixed is owed at the states in front of the batching.
  `k3Ok_of_leftOn`: **`K3LeftOn S.fork? heard h lm first Q s`, the shape's numbers in order, and φ
    holds what was heard: `K3Ok hd lm first (fixed9 φ s)`.** The snapshot's ledger is the state's;
    then `k3Ok_of_left` (Johnson/Top/H/Keep/RunsMember.lean). `kx_of_leftOn`: `kxAll` at `phiAll u
    psiAll`, from the promise at both seats. `leftOn_later`: the promise, carried to a state that
    has heard the same and holds a later ledger with its sizes.
  `heardDig s`: what the digits' lookup has left as heard. `leftOn_behind_digits`: **a yes of
    `K3.theStated`'s value at the digits' address, from a ledger with its sizes: `K3LeftOn` behind,
    at first := THE PLACE's PUBLIC NUMBER P'.first.** The lookup's own decision tests that the
    ledger's next free slot is that number: `decide_first` (Johnson/Top/H/K3DecideMore.lean).
  `leftOn_digits_front`, `leftOn_digits_head`: **that promise at every state reached at 14 l + 9 (l
    < 24), at 347, whose ledger is open and has its sizes.** `kxDigits_front`, `kxDigits_head`: **so
    the digits' half of `kxAll`, at jD := P'.first.** `kx_front`, `kx_head`: `kxAll` whole, the
    calls' half from LC.
PREMISES. The scope (hS, hR, `IM.Open`); hp: every sub-protocol of the first chain passes its test
on the plan; "reached"; hB: the ledger at the state is open and has its sizes; in the last two: LC,
okC: `K3LeftOn` at the calls' seat (what the table's item leftOn says; the batching's row asks that
item in front).
Limits. hp, hB, LC are shown of nothing here. The letter lm is free. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.SortLetters
import Johnson.Desc.First.Link.Law.SizesDigits
import Johnson.Top.H.Keep.RunsMember
import Johnson.Top.H.Keep.K3LeftAnyWords
import Johnson.Top.H.K3DecideMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.PhiAll
open VerifiableInference.OnPublicFiles (K3Ok Stood K3LeftOn k3Ok_of_left decide_left_some ok_of_shapeOf
        shape_some theStated_yes_digits quietAt_ledger seatDigits_keeps decide_first)
open VerifiableInference.Desc.First.Look (placeAt)
open Johnson.Desc.First.ForkMerge (headMergeDecide)
open Johnson.Desc.First.Walk.Tied (Reach StepYes stepYes_decide)
open OnBytes.Road.K4 (reach_pred)

/-- **THE PROMISE ON WHAT IS FIXED, FROM THE PROMISE ON THE STATE.** -/
theorem k3Ok_of_leftOn {α : Type} (φ : S → α) (hd : α → Option Forest.Heard)
    (heard : S → Option Forest.Heard) (hφ : ∀ e, hd (φ e) = heard e) {h : Forest.Shape}
    {lm first : ℕ} {Qf : Fork → Prop} {s : S} (L : K3LeftOn S.fork? heard h lm first Qf s)
    (hok : FoNums.ok h = true) : K3Ok hd lm first (fixed9 φ s) := by
  obtain ⟨F, F', G, g, rs, -, hn, hL, hg, hG, hl, hz⟩ := L
  intro g0 u0 e1 e2
  have e1' : heard s = some g0 := (hφ s).symm.trans e1
  obtain rfl : g = g0 := Option.some.inj (hg.symm.trans e1')
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 e2
  have eF : (pubOf b).F = G := Option.some.inj ((K9.get_fork s b hb).symm.trans hG)
  obtain ⟨a1, a2, rs', -, F0, u', hu', a3, a4⟩ :=
    k3Ok_of_left hL hok (pubOf b) (by rw [eF]; exact hl) (by rw [eF]; exact hz) g (pubOf b) rfl rfl
  obtain rfl : pubOf b = u' := Option.some.inj hu'
  rw [hn] at a3
  exact ⟨a1, a2, rs', e1, F0, pubOf b, e2, a3, a4⟩

/-- The promise, carried to a state that has heard the same and holds a later ledger. -/
theorem leftOn_later {heard : S → Option Forest.Heard} {h : Forest.Shape} {lm first : ℕ}
    {Qf : Fork → Prop} {s s' : S} (L : K3LeftOn S.fork? heard h lm first Qf s)
    (hh : heard s' = heard s) {G' : Fork} (hG' : s'.fork? = some G')
    (hl : ∀ G, s.fork? = some G → _root_.Fo.Later G G') (hz : Sized G') :
    K3LeftOn S.fork? heard h lm first Qf s' := by
  obtain ⟨F, F', G, g, rs, a1, a2, a3, a4, a5, a6, -⟩ := L
  exact ⟨F, F', G', g, rs, a1, a2, a3, hh.trans a4, hG', a6.trans (hl G a5), hz⟩

/-- What the digits' lookup has left as heard. -/
def heardDig (s : S) : Option Forest.Heard := s.tl?.bind (·.heard)

/-- **`kxAll` OF WHAT IS FIXED, FROM THE PROMISE AT BOTH SEATS.** -/
theorem kx_of_leftOn (u : HTailF2) {hC hD : Forest.Shape} {lmC jC lmD jD : ℕ}
    {QC QD : Fork → Prop} {s : S} (LC : K3LeftOn S.fork? S.lookHeard? hC lmC jC QC s)
    (okC : FoNums.ok hC = true) (LD : K3LeftOn S.fork? heardDig hD lmD jD QD s)
    (okD : FoNums.ok hD = true) : kxAll lmC jC lmD jD (fixed9 (phiAll u psiAll) s) :=
  ⟨k3Ok_of_leftOn (phiAll u psiAll) hdCalls S.lookHeard? (hdCalls_all u) LC okC,
    k3Ok_of_leftOn (phiAll u psiAll) hdDigits heardDig (hdDigits_all u) LD okD⟩

/-- **BEHIND A YES OF THE SEATED LOOKUP ON THE DIGITS.** -/
theorem leftOn_behind_digits {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block S Cl)
    (h : K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true) (i : ℕ)
    (hi : a.link = some i) (hpc : a.piece = K3.pieceAt X i true) (lm : ℕ) (s c : S)
    (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) (hd : B.decide s rs gs = .ok c)
    {F : Fork} (hF : s.fork? = some F) (hS : Sized F) :
    ∃ P' hh, placeAt X i true = some P' ∧ P'.shape = some hh ∧ FoNums.ok hh = true ∧
      K3LeftOn S.fork? heardDig hh lm P'.first (fun _ => True) c := by
  obtain ⟨P', sent, laid, n, gs', s', hP, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc s c rs gs hd
  cases hsh : P'.shape with
  | none =>
    exfalso
    obtain ⟨_, x, _, _, hx, _⟩ := VerifiableInference.OnPublicFiles.decide_ok (K3.seatDigits claim)
      a.piece laid sent P' [] s s' _ gs' hyes
    unfold K3.hear at hx
    simp [hsh] at hx
  | some hh =>
    obtain ⟨F₁, y, hF₁, hn, e, hE⟩ := decide_left_some (K3.seatDigits claim) a.piece laid sent P' []
      (K3.seatDigits_reads claim) hh hsh Reading.gl lm s s' _ gs' hyes
    obtain rfl : F = F₁ := Option.some.inj (hF.symm.trans hF₁)
    obtain ⟨rs', hL⟩ := hE hS
    have hsome : ((K3.seatDigits claim).fork s).isSome = true := by
      rw [hF₁]
      rfl
    have hy : s'.fork? = some y.2 := by
      rw [e]
      exact seatDigits_keeps claim _ _ _ hsome hn
    have hg : heardDig s' = some y.1 := by
      rw [e]
      exact K3.seatDigits_reads claim _ _ _ hsome hn
    obtain ⟨G, hG, hlat⟩ := later_behind_digits claim readers X codes shape a B h hOk i hi hpc s c
      rs gs hd hF hS
    refine ⟨P', hh, hP, hsh, ok_of_shapeOf (shape_some P' hh hsh), F, y.2, G, y.1, rs', trivial,
      decide_first (K3.seatDigits claim) a.piece laid sent P' [] s s' _ gs' F hF₁ hyes, hL, ?_, hG,
      ?_, hlat.sized hS⟩
    · rcases hstep with rfl | ⟨f, hf, hfs⟩
      · exact hg
      · show c.tl?.bind (·.heard) = _
        rw [quietAt_tl X i f hf s' c hfs]
        exact hg
    · rcases hstep with rfl | ⟨f, hf, hfs⟩
      · obtain rfl : y.2 = G := Option.some.inj (hy.symm.trans hG)
        exact _root_.Fo.Later.refl _
      · obtain ⟨F₂, k, hF₂, hG₂, -⟩ := quietAt_ledger X i f hf s' c hfs
        obtain rfl : y.2 = F₂ := Option.some.inj (hy.symm.trans hF₂)
        obtain rfl := Option.some.inj (hG₂.symm.trans hG)
        exact VerifiableInference.OnPublicFiles.later_planClaims y.2 k

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S}

/-- **RIGHT BEHIND THE DIGITS' SEATED SUB-PROTOCOL, AT EVERY LINK.** -/
theorem leftOn_digits_behind (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {l : ℕ} (hl : l < 25) {z : Q} {c' : S}
    (h : Reach 0 c.blocksInOrder start (14 * l + IM.k3Ix l true + 2 + 1) (z, c'))
    (hB : ∃ G', c'.fork? = some G' ∧ Sized G') (lm : ℕ) :
    ∃ P' hh, placeAt Bs.G₀.W l true = some P' ∧ P'.shape = some hh ∧ FoNums.ok hh = true ∧
      K3LeftOn S.fork? heardDig hh lm P'.first (fun _ => True) c' := by
  obtain ⟨Lk, b, b', e1, e2, e3, e4⟩ := IM.k3_of hS hR O l hl true
  obtain ⟨z', s, s'', b₀, e, hr, hb, hy⟩ := reach_pred h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  have hf : c.blocksInOrder[14 * l + IM.k3Ix l true + 2]? = some b := by
    rw [← IM.flatIx_scope hS hR O (by omega : l ≤ 24) (IM.k3Ix l true)]
    exact IM.hear_at_flat e1 e2
  obtain rfl : b = b₀ := Option.some.inj (hf.symm.trans hb)
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  have hd' := ((IM.yes_alone e4 (fun h => nomatch h) s _ rs gs).1 hd).1
  have hOk : b'.planOk = true := by
    rw [← IM.alone_planOk e4]
    exact hp b (List.mem_of_getElem? hf)
  have h7 : 7 ≤ (IM.k3Place l true).piece := by
    show 7 ≤ (if true = true then 6 else 1) + (if l = 24 then 1 else 0) + 1
    simp
  have hpc := piece_digits _ _ _ _ _ _ b' e3 l rfl h7
  obtain ⟨G, hG, hz⟩ := (sizes_behind_digits _ _ _ _ _ _ b' l e3 hOk rfl hpc s rs gs _ hd').pulls hB
  exact leftOn_behind_digits _ _ _ _ _ _ b' e3 hOk l rfl hpc lm s _ rs gs hd' hG hz

/-- **AT EVERY STATE REACHED IN FRONT OF THE BATCHING OF A LINK l < 24.** -/
theorem leftOn_digits_front (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {l : ℕ} (hl : l < 24) {z : Q} {c' : S}
    (h : Reach 0 c.blocksInOrder start (14 * l + 9) (z, c'))
    (hB : ∃ G', c'.fork? = some G' ∧ Sized G') (lm : ℕ) :
    ∃ P' hh, placeAt Bs.G₀.W l true = some P' ∧ P'.shape = some hh ∧ FoNums.ok hh = true ∧
      K3LeftOn S.fork? heardDig hh lm P'.first (fun _ => True) c' := by
  have i3 : IM.k3Ix l true = 6 := by
    show (if true = true then 6 else 1) + (if l = 24 then 1 else 0) = 6
    rw [if_neg (by omega : ¬ l = 24)]
    rfl
  exact leftOn_digits_behind hS hR O hp (by omega : l < 25) (by rw [i3]; exact h) hB lm

/-- **AT EVERY STATE REACHED IN FRONT OF THE HEAD's BATCHING.** -/
theorem leftOn_digits_head (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {z : Q} {c' : S}
    (h : Reach 0 c.blocksInOrder start 347 (z, c')) (hB : ∃ G', c'.fork? = some G' ∧ Sized G')
    (lm : ℕ) :
    ∃ P' hh, placeAt Bs.G₀.W 24 true = some P' ∧ P'.shape = some hh ∧ FoNums.ok hh = true ∧
      K3LeftOn S.fork? heardDig hh lm P'.first (fun _ => True) c' := by
  obtain ⟨z', s, s'', b₀, e, hr, hb, hy⟩ := reach_pred (k := 346) h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  obtain ⟨Lk, b, e1, e2, hla, -⟩ := IM.k11_of hS hR O
  have h3 := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by decide) 8] at h3
  obtain rfl : b = b₀ := Option.some.inj (h3.symm.trans hb)
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  have hm : headMergeDecide _ s rs = .ok _ := ((IM.k11_yes hla _ _ _ _).1 hd).1
  obtain ⟨G, hG, hz⟩ := merge_pulls _ hm hB
  obtain ⟨P', hh, a1, a0, a2, L⟩ := leftOn_digits_behind (start := start) hS hR O hp (l := 24)
    (by decide) (z := z) (c' := s) hr ⟨G, hG, hz⟩ lm
  obtain ⟨t1, G', t2, t3⟩ := merge_leaves_tl hm hG
  refine ⟨P', hh, a1, a0, a2, leftOn_later L (by show _ = _; unfold heardDig; rw [t1]) t2
    (fun G₀ hG₀ => ?_) (t3.sized hz)⟩
  obtain rfl : G = G₀ := Option.some.inj (hG.symm.trans hG₀)
  exact ⟨t3.next, t3.ns, t3.keep⟩

/-- **THE DIGITS' HALF OF `kxAll`, l < 24.** -/
theorem kxDigits_front (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {l : ℕ} (hl : l < 24) {z : Q} {c' : S}
    (h : Reach 0 c.blocksInOrder start (14 * l + 9) (z, c'))
    (hB : ∃ G', c'.fork? = some G' ∧ Sized G') (lm : ℕ) (u : HTailF2) :
    ∀ P', placeAt Bs.G₀.W l true = some P' →
      K3Ok hdDigits lm P'.first (fixed9 (phiAll u psiAll) c') := by
  intro P₀ hP₀
  obtain ⟨P', hh, a1, -, a2, L⟩ := leftOn_digits_front hS hR O hp hl h hB lm
  obtain rfl : P' = P₀ := Option.some.inj (a1.symm.trans hP₀)
  exact k3Ok_of_leftOn (phiAll u psiAll) hdDigits heardDig (hdDigits_all u) L a2

/-- **THE DIGITS' HALF OF `kxAll`, THE HEAD's LINK.** -/
theorem kxDigits_head (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {z : Q} {c' : S}
    (h : Reach 0 c.blocksInOrder start 347 (z, c')) (hB : ∃ G', c'.fork? = some G' ∧ Sized G')
    (lm : ℕ) (u : HTailF2) :
    ∀ P', placeAt Bs.G₀.W 24 true = some P' →
      K3Ok hdDigits lm P'.first (fixed9 (phiAll u psiAll) c') := by
  intro P₀ hP₀
  obtain ⟨P', hh, a1, -, a2, L⟩ := leftOn_digits_head hS hR O hp h hB lm
  obtain rfl : P' = P₀ := Option.some.inj (a1.symm.trans hP₀)
  exact k3Ok_of_leftOn (phiAll u psiAll) hdDigits heardDig (hdDigits_all u) L a2

/-- **`kxAll` WHOLE, l < 24.** -/
theorem kx_front (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {l : ℕ} (hl : l < 24) {z : Q} {c' : S}
    (h : Reach 0 c.blocksInOrder start (14 * l + 9) (z, c'))
    (hB : ∃ G', c'.fork? = some G' ∧ Sized G') (lm : ℕ) (u : HTailF2) {hC : Forest.Shape}
    {lmC jC : ℕ} {QC : Fork → Prop} (LC : K3LeftOn S.fork? S.lookHeard? hC lmC jC QC c')
    (okC : FoNums.ok hC = true) :
    ∀ P', placeAt Bs.G₀.W l true = some P' →
      kxAll lmC jC lm P'.first (fixed9 (phiAll u psiAll) c') := fun P' hP' =>
  ⟨k3Ok_of_leftOn (phiAll u psiAll) hdCalls S.lookHeard? (hdCalls_all u) LC okC,
    kxDigits_front hS hR O hp hl h hB lm u P' hP'⟩

/-- **`kxAll` WHOLE, THE HEAD's LINK.** -/
theorem kx_head (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {z : Q} {c' : S}
    (h : Reach 0 c.blocksInOrder start 347 (z, c')) (hB : ∃ G', c'.fork? = some G' ∧ Sized G')
    (lm : ℕ) (u : HTailF2) {hC : Forest.Shape} {lmC jC : ℕ} {QC : Fork → Prop}
    (LC : K3LeftOn S.fork? S.lookHeard? hC lmC jC QC c') (okC : FoNums.ok hC = true) :
    ∀ P', placeAt Bs.G₀.W 24 true = some P' →
      kxAll lmC jC lm P'.first (fixed9 (phiAll u psiAll) c') := fun P' hP' =>
  ⟨k3Ok_of_leftOn (phiAll u psiAll) hdCalls S.lookHeard? (hdCalls_all u) LC okC,
    kxDigits_head hS hR O hp h hB lm u P' hP'⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.k3Ok_of_leftOn
#print axioms VerifiableInference.Desc.LinkJoin.leftOn_later
#print axioms VerifiableInference.Desc.LinkJoin.kx_of_leftOn
#print axioms VerifiableInference.Desc.LinkJoin.leftOn_behind_digits
#print axioms VerifiableInference.Desc.LinkJoin.leftOn_digits_behind
#print axioms VerifiableInference.Desc.LinkJoin.leftOn_digits_front
#print axioms VerifiableInference.Desc.LinkJoin.leftOn_digits_head
#print axioms VerifiableInference.Desc.LinkJoin.kxDigits_front
#print axioms VerifiableInference.Desc.LinkJoin.kxDigits_head
#print axioms VerifiableInference.Desc.LinkJoin.kx_front
#print axioms VerifiableInference.Desc.LinkJoin.kx_head
