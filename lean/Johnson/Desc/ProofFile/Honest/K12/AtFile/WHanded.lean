-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WHanded.lean: the clauses `tidy` and `order` of `EndsRest` (WEnds.lean)
at a last chain's thread whose promise is `fillAt` at the start's own readers: the thread's clause (P)
holds them at the record that the letter `ends` names, and the start's one state ties that record to
the ends that the field names.

  `handLast`, `endedLast`   what the promise reads of the two ends: what the start reads
  `fillZ_is`       the library's `fillZ` at the second component is `fillAt` at these
  `one_start`      two yes of `start₃E` at one state: one statement, one shared end
  `handed_at_W`    at a stand: the letter's ends start the chain's first state, and `HandedOk` holds there
  `tidy_at_stand`  the statement in front of the test is tidy: in order, no open row a sample row
  `EndsLeft`       what stays of `EndsRest`
  `rest_of_left`   `EndsRest` from it, at a stand

By what. `shape_of_form` (WFive.lean); `shapeAt_inv`, `handedOk_of` (Johnson/Desc/Last/ShapeGives.lean);
`start_of_F0T` (WEnds.lean); `start₃E_st`, `start₃E_border`.

Limits. hPL is a premise: that the thread's promise is this term is the thread's letter.
NOT IN FRONT OF A LAW OVER COINS. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WEnds
import Johnson.Desc.Last.ShapeRowZero

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open OnBytes
open OnBytes.Means (Tidy InOrder)
open OnBytes.Slice (PlainRow)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Ground.Sh (stSh bookSh coreSh)
open VerifiableInference.Desc.Third (S₃ P₁₄ SharedOut start₃E firstOfS sharedOfEnd)
open VerifiableInference.Desc.Third.Law (start₃E_st start₃E_border)
open VerifiableInference.Desc.Last (fillAt HandedOk handedOk_of shapeAt_inv)
open H2K.Member (codesFull)
open ProofFile.Honest.K12.Light (ManyJob)
open ProofFile.Honest.LastThread (lettersLast)
open P5J (F0T TS)

/-- What the promise reads of the first chain's end. -/
def handLast (a : ProofFile.InstPub × TS) : Option VerifiableInference.Desc.Last.Handed := firstOfS a.2

/-- What the promise reads of the shared chain's end. -/
def endedLast (e : Desc.K14.St) : Option SharedOut := (Desc.K14.ended e).map sharedOfEnd

/-- The promise of the last chain's thread as the library lays it is this term. -/
theorem fillZ_is (p : P₁₄) (R : List Fmt.DeclaredRound) :
    VerifiableInference.Desc.Last.fillZ p R (fun q : ProofFile.InstPub × TS => q.2) =
      fillAt p R handLast endedLast := rfl

/-- **Two yes of the start at one state: one statement, one shared end.** -/
theorem one_start {codes codes' : Codes} {S S' : Params.LinShape} {st₁ st₂ : Statement}
    {book₁ book₂ : TreeBook} {roots₁ w₁ own₁ roots₂ w₂ own₂ : ℕ} {mask₁ mask₂ : Option ℕ}
    {pile₁ pile₂ : List TensorRow} {o o' : SharedOut} {s₀ : S₃}
    (h : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀)
    (h' : start₃E codes' S' st₂ book₂ roots₂ w₂ own₂ mask₂ pile₂ o' = .ok s₀) :
    st₁ = st₂ ∧ o = o' := by
  refine ⟨(start₃E_st _ _ _ _ _ _ _ _ _ _ _ h).symm.trans (start₃E_st _ _ _ _ _ _ _ _ _ _ _ h'), ?_⟩
  obtain ⟨g, hb⟩ := start₃E_border _ _ _ _ _ _ _ _ _ _ _ h
  obtain ⟨g', hb'⟩ := start₃E_border _ _ _ _ _ _ _ _ _ _ _ h'
  rw [hb] at hb'
  exact congrArg (·.shared) (Option.some.inj hb')

variable (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) {Bk : ProverCoinCounts}
  {W₀ Rc Tr X₀ X Wt : Type} (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
  (N : VerifiableInference.Desc.Shared.NumbersS)
  (Mg : Local W₀ Rc ProofFile.Inst Tr →
    VerifiableInference.Desc.Shared.MeaningS Desc.K14.St (ProofFile.InstPub × TS) Wt)
  (ML : VerifiableInference.Desc.Last.MeaningL S₃ Wt)
  (PL : VerifiableInference.Desc.Last.PromMeaningL Desc.K14.St S₃ (ProofFile.InstPub × TS))
  (order : S₃ → Prop) (taken : List Fmt.TreeSource)
  (ends : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn →
    (ProofFile.InstPub × TS) × Desc.K14.St)
  (wit : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table)
  (fixed : Fmt.TreeSource → ℕ) (item n₁ n₂ : ℕ) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : ℕ → Local W₀ Rc ProofFile.Inst Tr → S₃ → Prop)
  (Kp : VerifiableInference.Desc.Place → S₃ → S₃ → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **At a stand: the letter's ends start the chain's first state, and what they hand is in order.** -/
theorem handed_at_W {R : List Fmt.DeclaredRound}
    (hPL : PL = fillAt (ToldDesc.p14At Zp) R handLast endedLast) {k : Coins Bk} {st s₀ : S₃}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (u : Thr (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd Kp
      w).thread 2 k st m E)
    (hbeg : (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd Kp
      w).thread.begun k m.st.input (m.st.heard.take (lettersLast Zp Np cF H N Mg ML PL order taken
        ends wit table fixed item n₁ n₂ Vd Rd Kp w).thread.front) s₀) :
    ∃ f o, start₃E (ToldDesc.p14At Zp).codes (ToldDesc.p14At Zp).S f.st f.book f.roots f.w f.own
        f.mask f.pending o = .ok s₀ ∧ HandedOk (ToldDesc.p14At Zp) f o := by
  obtain ⟨-, -, hform, -⟩ := u
  obtain ⟨f', o', hf, ho, h2⟩ := shape_of_form _ hPL hform
  obtain ⟨f, e, hs, hd, h₀⟩ := start_of_F0T Zp Np cF hbeg
  have hf' : firstOfS (ends k m.st.input (m.st.heard.take (lettersLast Zp Np cF H N Mg ML PL order
      taken ends wit table fixed item n₁ n₂ Vd Rd Kp w).thread.front)).1.2 = some f' := hf
  have ho' : (Desc.K14.ended (ends k m.st.input (m.st.heard.take (lettersLast Zp Np cF H N Mg ML PL
      order taken ends wit table fixed item n₁ n₂ Vd Rd Kp w).thread.front)).2).map sharedOfEnd =
      some o' := ho
  have hd' : Desc.K14.ended (ends k m.st.input (m.st.heard.take (lettersLast Zp Np cF H N Mg ML PL
      order taken ends wit table fixed item n₁ n₂ Vd Rd Kp w).thread.front)).2 = some e := hd
  obtain rfl : f = f' := Option.some.inj (hs.symm.trans hf')
  rw [hd'] at ho'
  obtain rfl : sharedOfEnd e = o' := Option.some.inj ho'
  obtain ⟨s₁, -, ⟨hh, -⟩, -⟩ := shapeAt_inv h2
  exact ⟨f, sharedOfEnd e, h₀, handedOk_of hh⟩

/-- **At a stand the statement in front of the test is tidy.** -/
theorem tidy_at_stand {R : List Fmt.DeclaredRound}
    (hPL : PL = fillAt (ToldDesc.p14At Zp) R handLast endedLast) {k : Coins Bk} {st : S₃}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (u : Thr (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd Kp
      w).thread 2 k st m E) : Tidy st.st := by
  obtain ⟨-, -, hform, -⟩ := u
  obtain ⟨f', o', -, -, h2⟩ := shape_of_form _ hPL hform
  obtain ⟨⟨s₁, B⟩, -⟩ := VerifiableInference.Desc.Last.behindOk_of_two h2
  exact B.tidy

section
variable {W' X' : Type}

/-- **What stays of `EndsRest`** where the promise holds the rest. -/
structure EndsLeft (p : P₁₄) (A : ManyJob W' X') (f : VerifiableInference.Desc.Last.Handed)
    (o : SharedOut) (s₀ : S₃) : Prop where
  members : ∀ G, s₀.st.groups[s₀.loc.own]? = some G → ∀ m ∈ G.members.toList,
    ∀ x : OnBytes.Oracle, s₀.st.oracles[m]? = some x → ∀ r ∈ x.sampleRows.toList, PlainRow r
  omega : ∀ y, o.st.oracles[o.omega]? = some y → ∀ r ∈ y.sampleRows.toList, PlainRow r
  line : (doorOwnSh p.S f.own f.mask (stSh o.st) (bookSh o.book) o.omega
    (coreSh ⟨f.st, f.book, f.roots⟩)).any (linesB A codesFull 3) = true

/-- **`EndsRest` from what stays.** f, o: at the ends that the field names; f', o': at the letter's. -/
theorem rest_of_left {p : P₁₄} {A : ManyJob W' X'} {f f' : VerifiableInference.Desc.Last.Handed}
    {o o' : SharedOut} {s₀ : S₃}
    (h : start₃E p.codes p.S f.st f.book f.roots f.w f.own f.mask f.pending o = .ok s₀)
    (h' : start₃E p.codes p.S f'.st f'.book f'.roots f'.w f'.own f'.mask f'.pending o' = .ok s₀)
    (hk : HandedOk p f' o') (L : EndsLeft p A f o s₀) : EndsRest p A f o s₀ := by
  obtain ⟨e₁, e₂⟩ := one_start h h'
  exact ⟨by rw [e₁]; exact hk.tidy, by rw [e₂]; exact hk.order₂, L.members, L.omega, L.line⟩

end

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.handLast
#print axioms ProofFile.Honest.K12.AtFile.endedLast
#print axioms ProofFile.Honest.K12.AtFile.fillZ_is
#print axioms ProofFile.Honest.K12.AtFile.one_start
#print axioms ProofFile.Honest.K12.AtFile.handed_at_W
#print axioms ProofFile.Honest.K12.AtFile.tidy_at_stand
#print axioms ProofFile.Honest.K12.AtFile.EndsLeft
#print axioms ProofFile.Honest.K12.AtFile.rest_of_left
