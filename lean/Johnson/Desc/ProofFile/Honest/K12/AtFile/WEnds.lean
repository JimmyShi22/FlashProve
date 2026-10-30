-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WEnds.lean: the clauses `lines` and `front` of `StandAtW`
(WAccepted.lean), at the library's description, from what the two earlier chains hand over.

  `EndsOwe`, `EndsRest`   what the two ends owe, each under its name; what stays of it where the
                   first chain's fold stands
  `owe_of_rest`    `rows`, `ord` off the fold: `openRowsPass_reached`, `openOrd_reached`
  `front_of_ends`  `linesB` and `FrontAsksD` at the state on entry, from the start's yes, the block's
                   yes and `EndsOwe`: `door_own_shape` (WShape.lean), `rows_at_own` (WFrontAsks.lean),
                   `frontAsksD_of_five`
  `start_of_F0T`   a yes of the description's start is `start₃E` at what the first chain's last record
                   names and at the shared chain's end
  `made_at_W`      `Thread.Made` at number 2 gives the chain's first state, the block's yes and that the
                   taken sources are tied
  `lines_front_at_W`   the two clauses at a stand

The premise hOwe of `lines_front_at_W`. At a stand, at the ends that the field names, `EndsRest`: `tidy`,
`order` are in the thread's clause (P) by `HandedOk`, where `ends` is those ends; `members`, `omega` are
the plain sample rows; `line` is the public test at a term of the first chain's last shape: closed by
a literal and a tie to the run on shapes, neither laid here.

Limits.
- NOT IN FRONT OF A LAW OVER COINS: `lines_front_at_W` stands behind `Thr`.
- `line` can be false; nothing here says that it is true.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WTreesSentBeforeTest
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WLetter
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WShape
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontAsks
import Johnson.Desc.Plain.StartThreeAtPure
import Johnson.Desc.Third.Law.Sources

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K12
open OnBytes OnBytes.Slice
open OnBytes.Means (Tidy InOrder)
open VerifiableInference.Desc (Block Chain foldBlocks)
open VerifiableInference.Desc.Ground.Sh (stSh bookSh coreSh)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃ P₁₄ SharedOut batchLinearConstraintsSecondPart takenSources start₃E firstOfS
  sharedOfEnd start₃F)
open VerifiableInference.Desc.Third.Law (takenSources_same)
open H2K.Member (codesFull)
open ProofFile.Honest.Sh (testSh)
open ProofFile.Honest.K12.Light (ManyJob)
open ProofFile.Honest.LastThread (lettersLast)
open Johnson.AtFull.Shape (OpenOrd)
open ToldDesc (ownAt)
open P5J (F0T TS AtMgA)

section
variable {W X : Type}

/-- **What the two ends owe.** p: the last chain's numbers. A: the job. f: what the first chain's last
record names. o: of the shared chain's end. s₀: the chain's first state. -/
structure EndsOwe (p : P₁₄) (A : ManyJob W X) (f : VerifiableInference.Desc.Last.Handed) (o : SharedOut) (s₀ : S₃) : Prop where
  tidy : Tidy f.st
  order : OnBytes.Means.InOrder o.st
  rows : OpenRowsPass f.st
  ord : OpenOrd f.st
  members : ∀ G, s₀.st.groups[s₀.loc.own]? = some G → ∀ m ∈ G.members.toList,
    ∀ x : OnBytes.Oracle, s₀.st.oracles[m]? = some x → ∀ r ∈ x.sampleRows.toList, PlainRow r
  omega : ∀ y, o.st.oracles[o.omega]? = some y → ∀ r ∈ y.sampleRows.toList, PlainRow r
  line : (doorOwnSh p.S f.own f.mask (stSh o.st) (bookSh o.book) o.omega
    (coreSh ⟨f.st, f.book, f.roots⟩)).any (linesB A codesFull 3) = true

/-- **What stays of `EndsOwe`** where the first chain's fold stands: `rows`, `ord` come off it. -/
structure EndsRest (p : P₁₄) (A : ManyJob W X) (f : VerifiableInference.Desc.Last.Handed) (o : SharedOut)
    (s₀ : S₃) : Prop where
  tidy : Tidy f.st
  order : OnBytes.Means.InOrder o.st
  members : ∀ G, s₀.st.groups[s₀.loc.own]? = some G → ∀ m ∈ G.members.toList,
    ∀ x : OnBytes.Oracle, s₀.st.oracles[m]? = some x → ∀ r ∈ x.sampleRows.toList, PlainRow r
  omega : ∀ y, o.st.oracles[o.omega]? = some y → ∀ r ∈ y.sampleRows.toList, PlainRow r
  line : (doorOwnSh p.S f.own f.mask (stSh o.st) (bookSh o.book) o.omega
    (coreSh ⟨f.st, f.book, f.roots⟩)).any (linesB A codesFull 3) = true

/-- **The lines and the front's hypotheses at the state on entry.** -/
theorem front_of_ends {Cl : Type} (p : P₁₄) (A : ManyJob W X) (w : W) (fr : Front X) {f : VerifiableInference.Desc.Last.Handed}
    {o : SharedOut} {s₀ s : S₃} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (h₀ : start₃E p.codes p.S f.st f.book f.roots f.w f.own f.mask f.pending o = .ok s₀)
    (h₁ : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s₀ rs gs = .ok s)
    (h₂ : enterOwn s = .ok (A.rec₀ w fr)) (he : A.p.early = true) (E : EndsOwe p A f o s₀) :
    linesB A codesFull 3 (testSh (A.rec₀ w fr)) = true ∧
      ∃ Dp, FrontAsksD A.toRun.toTest w fr codesFull Dp := by
  have hl : linesB A codesFull 3 (testSh (A.rec₀ w fr)) = true := by
    have k := E.line
    rw [door_own_shape p h₀ h₁ h₂] at k
    exact k
  have h5 : frontFiveB A.p codesFull (testSh (A.rec₀ w fr)) = true := by
    have k := hl
    unfold linesB at k
    simp only [Bool.and_eq_true] at k
    exact k.1.1
  obtain ⟨ht, hd, hc⟩ := rows_at_own p h₀ h₁ h₂ E.tidy E.order E.rows E.ord E.members E.omega
  exact ⟨hl, frontAsksD_of_five A.toRun.toTest w fr codesFull he h5 ht hd hc⟩

end

variable (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)

/-- What the first chain hands is its last record's. -/
theorem st_of_firstOfS {e₁ : TS} {f : VerifiableInference.Desc.Last.Handed}
    (h : firstOfS e₁ = some f) : f.st = e₁.st := by
  unfold firstOfS at h
  obtain ⟨e, -, rfl⟩ := Option.map_eq_some_iff.1 h
  rfl

/-- **`EndsOwe` from what stays**, at the first chain's fold to its end. -/
theorem owe_of_rest {W X : Type} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {x : VerifiableInference.Desc.First.Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {q : ProofFile.InstPub} {e₁ : TS} {r₁ : List Fmt.RoundView} {c₁ : List VerifiableInference.Desc.OpenedColumn}
    (hf : foldBlocks 0 (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
      ((F0T OnBytes.secondHashFunction Zp Np cF).start₁ q) r₁ c₁ = .ok (e₁, [], []))
    {p : P₁₄} {A : ManyJob W X} {f : VerifiableInference.Desc.Last.Handed} {o : SharedOut} {s₀ : S₃}
    (hs : firstOfS e₁ = some f) (R : EndsRest p A f o s₀) : EndsOwe p A f o s₀ := by
  have hf' : foldBlocks 0 (cF.blocksInOrder.take cF.blocksInOrder.length) (ProofFile.startS Zp q) r₁ c₁ =
      .ok (e₁, [], []) := by
    rw [List.take_length]
    exact hf
  have e : f.st = e₁.st := st_of_firstOfS hs
  exact ⟨R.tidy, R.order, by rw [e]; exact openRowsPass_reached h _ 0 q r₁ c₁ _ hf',
    by rw [e]; exact Johnson.AtFull.Shape.openOrd_reached h _ 0 q r₁ c₁ _ hf', R.members, R.omega,
    R.line⟩

/-- **A yes of the description's start.** -/
theorem start_of_F0T {q : ProofFile.InstPub} {e₁ : TS} {e₂ : Desc.K14.St} {s₀ : S₃}
    (h : (F0T OnBytes.secondHashFunction Zp Np cF).start₃ q e₁ e₂ = .ok s₀) :
    ∃ f e, firstOfS e₁ = some f ∧ Desc.K14.ended e₂ = some e ∧
      start₃E (ToldDesc.p14At Zp).codes (ToldDesc.p14At Zp).S f.st f.book f.roots f.w f.own f.mask f.pending
        (sharedOfEnd e) = .ok s₀ := by
  have h' : ((ProofFile.seatedAt OnBytes.secondHashFunction Zp Np cF).start₃ q e₁ e₂).toOption = some s₀ := by
    show ((F0T OnBytes.secondHashFunction Zp Np cF).start₃ q e₁ e₂).toOption = some s₀
    rw [h]
    rfl
  obtain ⟨e, hd, hs⟩ := ProofFile.hstart_at OnBytes.secondHashFunction Zp Np cF (fun x => x) (fun _ _ => rfl) q e₁ e₂
    s₀ h'
  have hs' : start₃F (ToldDesc.p14At Zp) firstOfS sharedOfEnd q e₁ e = .ok s₀ := hs
  unfold start₃F at hs'
  cases hf : firstOfS e₁ with
  | none =>
    rw [hf] at hs'
    cases hs'
  | some f =>
    rw [hf] at hs'
    exact ⟨f, e, rfl, hd, hs'⟩

section
variable {Bk : ProverCoinCounts} {W₀ Rc Tr X₀ X Wt : Type}
  (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
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

/-- **`Thread.Made` at number 2: the chain's first state and the block's yes.** -/
theorem made_at_W {k : Coins Bk} {st : S₃} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hM : (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd Kp
      w).thread.Made 2 k st m E) :
    ∃ s₀ rs gs, (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd
        Kp w).thread.begun k m.st.input (m.st.heard.take (lettersLast Zp Np cF H N Mg ML PL order
          taken ends wit table fixed item n₁ n₂ Vd Rd Kp w).thread.front) s₀ ∧
      (batchLinearConstraintsSecondPart (Cl := Unit) (ToldDesc.p14At Zp)).decide s₀ rs gs = .ok st ∧
      VerifiableInference.Desc.Third.Law.Tied (ownAt Np) st := by
  obtain ⟨-, -, -, -, s₀, cols, hbeg, -, hf⟩ := hM
  have e : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.take 2 =
      [((batchLinearConstraintsSecondPart (ToldDesc.p14At Zp) : Block S₃ Unit).retype : Block S₃ ProofFile.Cl),
        ((takenSources (ownAt Np) : Block S₃ Unit).retype : Block S₃ ProofFile.Cl)] := by
    rw [second_flat]
    rfl
  have hf' := hf
  change foldBlocks (F0T OnBytes.secondHashFunction Zp Np cF).lastChainFirstTreeNumber
    ((F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.take 2) s₀ _ cols = .ok (st, [], []) at hf'
  rw [e] at hf'
  obtain ⟨s₁, r₁, g₁, r₂, g₂, h1, h2⟩ := fold_two _ _ _ _ _ _ _ hf'
  have h2' : (takenSources (ownAt Np) : Block S₃ Unit).decide s₁ r₂ g₂ = .ok st := h2
  obtain ⟨rfl, hT⟩ := (VerifiableInference.Desc.Third.Law.takenSources_exact (ownAt Np) s₁ r₂ g₂ st).1 h2'
  exact ⟨s₀, r₁, g₁, hbeg, h1, hT⟩

/-- **The clauses `lines` and `front` at a stand.** -/
theorem lines_front_at_W {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {x : VerifiableInference.Desc.First.Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (A : ManyJob (Local W₀ Rc ProofFile.Inst Tr) X) (he : A.p.early = true) {k : Coins Bk} {st : S₃}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hF : FieldAtW (F0T OnBytes.secondHashFunction Zp Np cF) (lettersLast Zp Np cF H N Mg ML PL order taken ends
                  wit table fixed item n₁ n₂ Vd Rd Kp w).thread Said 2)
    (u : ThrS (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd Kp
      w).thread Said 2 k st m E)
    (hE : enterOwn st = .ok (A.rec₀ m.st.input (frontOf m)))
    (hOwe : ∀ base e₁ e₂ f e s₀, (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed
        item n₁ n₂ Vd Rd Kp w).thread.begun k m.st.input (m.st.heard.take (lettersLast Zp Np cF H N Mg
          ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd Kp w).thread.front) s₀ →
      EndsAre (F0T OnBytes.secondHashFunction Zp Np cF) m base e₁ e₂ → firstOfS e₁ = some f → Desc.K14.ended e₂ = some e →
      start₃E (ToldDesc.p14At Zp).codes (ToldDesc.p14At Zp).S f.st f.book f.roots f.w f.own f.mask
        f.pending (sharedOfEnd e) = .ok s₀ →
      EndsRest (ToldDesc.p14At Zp) A f (sharedOfEnd e) s₀) :
    linesB A codesFull 3 (testSh (A.rec₀ m.st.input (frontOf m))) = true ∧
      ∃ Dp, FrontAsksD A.toRun.toTest m.st.input (frontOf m) codesFull Dp := by
  obtain ⟨base, cols, e₁, e₂, hEn, -, -, hs⟩ := hF k st m E u
  obtain ⟨⟨-, -, -, -, hM, -, -⟩, -⟩ := u
  obtain ⟨s₀, rs, gs, hbeg, h₁, -⟩ := made_at_W Zp Np cF H N Mg ML PL order taken ends wit table
    fixed item n₁ n₂ Vd Rd Kp w hM
  obtain ⟨f, e, hf, hd, h₀⟩ := start_of_F0T Zp Np cF (hs s₀ hbeg)
  have R := hOwe base e₁ e₂ f e s₀ hbeg hEn hf hd h₀
  obtain ⟨r₁, r₂, rest, c₁, c₂, -, -, -, -, -, -, f₁, -⟩ := hEn
  exact front_of_ends (ToldDesc.p14At Zp) A m.st.input (frontOf m) h₀ h₁ hE he
    (owe_of_rest Zp Np cF h f₁ hf R)

end

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.EndsOwe
#print axioms ProofFile.Honest.K12.AtFile.EndsRest
#print axioms ProofFile.Honest.K12.AtFile.front_of_ends
#print axioms ProofFile.Honest.K12.AtFile.st_of_firstOfS
#print axioms ProofFile.Honest.K12.AtFile.owe_of_rest
#print axioms ProofFile.Honest.K12.AtFile.start_of_F0T
#print axioms ProofFile.Honest.K12.AtFile.made_at_W
#print axioms ProofFile.Honest.K12.AtFile.lines_front_at_W
