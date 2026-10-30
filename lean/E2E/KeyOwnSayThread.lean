-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyOwnSayThread.lean: the clause `say` of `OwnAsks` at a stand of the last thread at border 2: the rows that the own test takes in hold of the job's
words. The open rows come from the item `rows`; the first chain's sample rows from the pins' sentences 'srow 0', 'srow 2'; Omega's from the shared
chain's sample sentence, at its new number.

  `srow_to`, `say_core`: at the records.
  `say_stand`: at a stand.

Left as premises: ho₀, ho₂: the plan's numbers of messages 0 and 2. Omega's sample sentence comes from the item (pin o_omega) that stands open at border 2. `htie`: THE TIE: the
chain's words on the members' tables are the job's. `hsame`.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyOwnSayAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.KeyLastChain
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.K12 (wordsAt PlainRows)
open OnBytes (TableKey Part Oracle Group)
open OnBytes.Means (Words Says tableSize AllSay layoutOf)
open OnBytes.Slice (GE rdE readE begun runRows)
open VerifiableInference.Desc (Place Wit OpenedColumn Strs)
open VerifiableInference.Desc.Ground.Sh (stTidyB tidy_of stSh grpSh grp_get orcSh)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃ Border)
open VerifiableInference.Desc.Third.Law (RowsHold law_k14Second)
open VerifiableInference.Desc.Last (ItemL)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces descriptionFromSource thirdPar valOf RowHolds)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeyThread (KeyFill)
open AtPublicFiles.AtFiles (KeySourced ThirdShaped Sh₃ sh₃ SF CF borderSh)
open AtPublicFiles.AtFiles.Full (A0)
open Johnson.RunOne.KeyRows1 (plan₁)

/-- **The sample sentence at a known number.** -/
theorem srow_to {T : OnBytes.Statement} {num : Option Nat} {oo : Nat} {same : OnBytes.E → OnBytes.E → Prop}
    {val : Nat → Part → Nat → OnBytes.E} (ho : num = some oo) (hsame : same = fun a b => readE a = readE b)
    (h : ∃ (o' : Nat) (x' : Oracle), num = some o' ∧ T.oracles[o']? = some x' ∧ x'.sampled = true ∧
      x'.sampleRows.size ≠ 0 ∧ ∀ r ∈ x'.sampleRows.toList, RowHolds same T val r) :
    ∀ x : Oracle, T.oracles[oo]? = some x → ∀ r ∈ x.sampleRows.toList,
      RowHolds (fun a b => readE a = readE b) T val r := by
  obtain ⟨o', x', ho', hx', -, -, hr'⟩ := h
  obtain rfl : oo = o' := Option.some.inj (ho.symm.trans ho')
  intro x hx r hr
  obtain rfl : x' = x := Option.some.inj (hx'.symm.trans hx)
  rw [← hsame]
  exact hr' r hr

/-- **The clause at the records**: from the two first chain's sample sentences at the reading val, Omega's at the shared half, and the open rows. -/
theorem say_core {Wt₁ : Type} (val₁ : Wt₁ → Nat → Part → Nat → GE) (p : VerifiableInference.Desc.Third.P₁₄) {s₀ st : S₃} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (hdec : (VerifiableInference.Desc.Third.batchLinearConstraintsSecondPart (Cl := Unit) p).decide s₀ rs gs = .ok st)
    (hsh₀ : sh₃ SF s₀ = A0) (hsh₂ : sh₃ SF st = A2) (u : Wt₁ × Words GE) (val : Nat → Part → Nat → OnBytes.E)
    (hv : ∀ o pt i, val₁ u.1 o pt i = readE (val o pt i))
    (h0 : ∀ x : Oracle, s₀.st.oracles[0]? = some x → ∀ r ∈ x.sampleRows.toList,
      RowHolds (fun a b => readE a = readE b) s₀.st val r)
    (h9 : ∀ x : Oracle, s₀.st.oracles[9]? = some x → ∀ r ∈ x.sampleRows.toList,
      RowHolds (fun a b => readE a = readE b) s₀.st val r)
    (hOm : ∀ b : Border, s₀.loc.border = some b → ∀ y : Oracle, b.shared.st.oracles[b.shared.omega]? = some y →
      ∀ r ∈ y.sampleRows.toList, Says rdE b.shared.st r u.2)
    (hrows : RowsHold rdE st (wordsKey val₁ st u))
    {t : T12} (he : enterOwn st = .ok t) (R : PlainRows)
    (htie : ∀ G, st.st.groups[st.loc.own]? = some G → ∀ o ∈ G.members.toList, ∀ pt, ∀ i < tableSize st.st o pt,
      wordsKey val₁ st u o pt i = wordsAt (begun st.st st.loc.own G) (layoutOf st.st G) R o pt i) :
    ∀ G, t.st.groups[t.g]? = some G →
      AllSay rdE (begun t.st t.g G) (runRows t.st G).toList (wordsAt (begun t.st t.g G) (layoutOf t.st G) R) := by
  have ht₂ : stTidyB st.st = true := (congrArg (fun a : Sh₃ => a.2.tidy) hsh₂).trans tidy_A2
  have ht₀ : stTidyB s₀.st = true := (congrArg (fun a : Sh₃ => a.2.tidy) hsh₀).trans tidy_A0
  have hk := (law_k14Second (Cl := Unit) p).1 _ _ _ _ hdec
  have hsay := (law_k14Second (Cl := Unit) p).2 _ _ _ _ hdec
  obtain ⟨b, hb⟩ : ∃ b, s₀.loc.border = some b := by
    obtain ⟨b, _, _, _, hb', _⟩ := hsay
    exact ⟨b, hb'⟩
  have hbt : stTidyB b.shared.st = true := by
    have q : (sh₃ SF s₀).2.border.map (·.tidy) = some true := by
      rw [hsh₀]
      exact tidy_border_A0
    have q' : (s₀.loc.border.map (borderSh SF s₀.st.codes)).map (·.tidy) = some true := q
    rw [hb] at q'
    exact Option.some.inj q'
  have hbo : b.shared.omega = 2 := by
    have q : (sh₃ SF s₀).2.border.map (·.omega) = some 2 := by
      rw [hsh₀]
      exact omega_border_A0
    have q' : (s₀.loc.border.map (borderSh SF s₀.st.codes)).map (·.omega) = some 2 := q
    rw [hb] at q'
    exact Option.some.inj q'
  have hc₀ : s₀.st.codes = CF := (congrArg (fun a : Sh₃ => a.1.st.codes) hsh₀).trans codes_A0
  have hc : b.shared.st.codes = s₀.st.codes := by
    have q : (sh₃ SF s₀).2.border.map (·.st.codes) = some CF := by
      rw [hsh₀]
      exact codes_border_A0
    have q' : (s₀.loc.border.map (borderSh SF s₀.st.codes)).map (·.st.codes) = some CF := q
    rw [hb] at q'
    exact (Option.some.inj q').trans hc₀.symm
  have hlen : s₀.st.oracles.size = A0.1.st.oracles.length := by
    have q : (stSh s₀.st).oracles.length = A0.1.st.oracles.length :=
      congrArg (fun a : Sh₃ => a.1.st.oracles.length) hsh₀
    rw [← q]
    show _ = (s₀.st.oracles.toList.map orcSh).length
    simp
  have h9' : 9 < s₀.st.oracles.size := by
    rw [hlen]
    exact below_A0
  have hom : st.loc.omega = s₀.st.oracles.size := by
    obtain ⟨_, _, _, _, _, hl, _⟩ := hsay
    rw [hl]
  have hne : ∀ z < s₀.st.oracles.size, z ≠ st.loc.omega := fun z hz => by
    rw [hom]
    omega
  have hI₀ := (tidy_of ht₀).inOrder
  have hsam := samples_behind p s₀ st hsay hk [0, 9] (wordsKey val₁ st u) u.2 b hb hI₀ (tidy_of hbt).inOrder hc
    (fun o' ho' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho'
      rcases ho' with rfl | rfl <;> omega)
    (fun o' ho' x hx r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho'
      rcases ho' with rfl | rfl
      · exact srow_says val₁ s₀.st st u val hv hI₀ 0 x hx hne r hr (h0 x hx r hr)
      · exact srow_says val₁ s₀.st st u val hv hI₀ 9 x hx hne r hr (h9 x hx r hr))
    (hOm b hb)
    (fun pt i => by
      rw [hbo]
      unfold wordsKey
      rw [if_pos hom.symm])
  refine say_at_entry he (tidy_of ht₂).inOrder (tidy_of ht₂).kinds _ R hrows (fun G hG o' ho' x hx r hr => ?_) htie
  have hmem : G.members.toList = [0, 9, st.loc.omega] := by
    have q := members_A2
    rw [← hsh₂] at q
    have q' : ((stSh st.st).groups[st.loc.own]?).map (·.members) = some [0, 9, st.loc.omega] := q
    rw [grp_get, hG] at q'
    exact Option.some.inj q'
  rw [hmem] at ho'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho'
  rcases ho' with rfl | rfl | rfl
  · exact hsam 0 (Or.inl (by simp)) x hx r hr
  · exact hsam 9 (Or.inl (by simp)) x hx r hr
  · exact hsam _ (Or.inr hom) x hx r hr

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk Cells M Smp Rec P₂ Wt₂ : Type} {Z : VerifierAndGoals.PublicFiles}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk)
  (L : KeyFill Bk W₀ Rc Cells M Smp Rec)
  (ℓ₂ : WitLens Wt₂) (Nm : NumbersS)
  (Mg₂ : Common W₀ Rc TableKey → MeaningS St P₂ Wt₂)
  (tb₂ : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest₂ : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt₂)
  (Kp₂ : Nat → St → St → Prop) (Vd₂ : Common W₀ Rc TableKey → Prop)
  (w₂ : Common W₀ Rc TableKey) (w₀ : W₀) (rc : Rc) (x : Xi)
  (hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X))
  (tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
  (Said₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X → Prop)
  (Said₂ : Nat → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
  (d : (Xi × FirstState) × St)
  (Dt : Local W₀ Rc Xi Unit → MeaningS St (Xi × FirstState) (Wit Cells Unit M × Words Cb.Gl.E))
  (n₁ n₂ : Nat) (Vd : Local W₀ Rc Xi Unit → Prop) (w : Local W₀ Rc Xi Unit)
  (dfltT : Place × Table) (dfltM : Mid (Local W₀ Rc Xi Unit) X)

set_option maxHeartbeats 1000000 in
/-- **The clause at a stand.** -/
theorem say_stand (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hZ : ThirdShaped (X := Xs) (N := Nr) (P := Pl) (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM) (fun _ _ _ => true) A0)
    (hsame : L.R.same = fun a b => readE a = readE b)
    (ho₀ : (plan₁ (AtPublicFiles.KeyThread.one₀ Xs)).orc 0 = some 0) (ho₂ : (plan₁ (AtPublicFiles.KeyThread.one₀ Xs)).orc 2 = some 9)
    {k : Coins Bk} {st : S₃} {m : Mid (Local W₀ Rc Xi Unit) X} {E : Env} (ds : List Fmt.Drawn)
    (hT : Thr (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM) 2 k st m E)
    {t : T12} (he : enterOwn st = .ok t) (R : PlainRows)
    (htie : ∀ G, st.st.groups[st.loc.own]? = some G → ∀ o ∈ G.members.toList, ∀ pt, ∀ i < tableSize st.st o pt,
      wordsKey (val₁Key Xs L) st ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).wit k m.st.input (m.st.heard ++ ds)) o pt i =
        wordsAt (begun st.st st.loc.own G) (layoutOf st.st G) R o pt i) :
    ∀ G, t.st.groups[t.g]? = some G →
      AllSay rdE (begun t.st t.g G) (runRows t.st G).toList (wordsAt (begun t.st t.g G) (layoutOf t.st G) R) := by
  have hsh₂ := shape_own hs scope rfl hZ hT
  obtain ⟨s₀, rs, gs, hbeg, hdec⟩ := two_steps rfl hT
  have hsh₀ : sh₃ SF s₀ = A0 := by
    have q := hZ.first _ _ _ _ hT.2.2.2.2.2.2 hbeg
    obtain ⟨-, -, hlin, -⟩ := AtPublicFiles.AtFiles.Full.first_of_sourced hs scope fun _ _ _ _ => true
    have hS : Xs.chains.made.sized.key.once.shape = SF := hlin.symm.trans (AtPublicFiles.AtFiles.Full.six_sourced hs scope).lin
    have q' : sh₃ Xs.chains.made.sized.key.once.shape s₀ = A0 := q
    rw [hS] at q'
    exact q'
  obtain ⟨h, o, hh₁, ho₁, hst⟩ := (AtPublicFiles.KeyLastThread.start_key Xs Nr Pl _ _ _ s₀).1 hbeg
  have hh₂ := hh₁
  change (((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).seat k m st).1.1.2).lin.map
    (AtPublicFiles.KeyLastThread.handOf ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).seat k m st).1.1.2) = some h at hh₂
  obtain ⟨l, -, rfl⟩ := Option.map_eq_some_iff.1 hh₂
  obtain ⟨⟨gb, hgb⟩, -, -, -, est, -⟩ := K14.start_gives (thirdPar Xs.chains) _ o s₀ hst
  have e₀ : ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).seat k m st).1.1.2.d.st = s₀.st := est.symm
  have hiI : ItemL.pinI ∈ (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).opened 2 := by
    show ItemL.pinI ∈ fwdOpen VerifiableInference.Desc.Last.startLast LastRows.rows 2
    decide
  have hiV : ItemL.pinV ∈ (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).opened 2 := by
    show ItemL.pinV ∈ fwdOpen VerifiableInference.Desc.Last.startLast LastRows.rows 2
    decide
  have hiR : ItemL.rows ∈ (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).opened 2 := by
    show ItemL.rows ∈ fwdOpen VerifiableInference.Desc.Last.startLast LastRows.rows 2
    decide
  have p₀ : ∃ (o' : Nat) (x' : Oracle), (plan₁ (AtPublicFiles.KeyThread.one₀ Xs)).orc 0 = some o' ∧
      ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).seat k m st).1.1.2.d.st.oracles[o']? = some x' ∧ x'.sampled = true ∧ x'.sampleRows.size ≠ 0 ∧
      ∀ r ∈ x'.sampleRows.toList, RowHolds L.R.same ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).seat k m st).1.1.2.d.st
        (valOf (plan₁ (AtPublicFiles.KeyThread.one₀ Xs)) L.R ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).wit k m.st.input (m.st.heard ++ ds)).1) r :=
    ((hT.2.2.2.1 ds ItemL.pinI hiI).1 rfl).2
  have p₂ : ∃ (o' : Nat) (x' : Oracle), (plan₁ (AtPublicFiles.KeyThread.one₀ Xs)).orc 2 = some o' ∧
      ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).seat k m st).1.1.2.d.st.oracles[o']? = some x' ∧ x'.sampled = true ∧ x'.sampleRows.size ≠ 0 ∧
      ∀ r ∈ x'.sampleRows.toList, RowHolds L.R.same ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).seat k m st).1.1.2.d.st
        (valOf (plan₁ (AtPublicFiles.KeyThread.one₀ Xs)) L.R ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).wit k m.st.input (m.st.heard ++ ds)).1) r :=
    ((hT.2.2.2.1 ds ItemL.pinV hiV).2 rfl).2
  have hiO : ItemL.pinO ∈ (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).opened 2 := by
    show ItemL.pinO ∈ fwdOpen VerifiableInference.Desc.Last.startLast LastRows.rows 2
    decide
  have pO : _root_.Desc.K14.Honest.SmpOwn 2 ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).seat k m st).1.2
      ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).wit k m.st.input (m.st.heard ++ ds)).2 := (hT.2.2.2.1 ds ItemL.pinO hiO) .oOmega rfl
  have hOm : ∀ b : Border, s₀.loc.border = some b → ∀ y : Oracle, b.shared.st.oracles[b.shared.omega]? = some y →
      ∀ r ∈ y.sampleRows.toList, Says rdE b.shared.st r ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).wit k m.st.input (m.st.heard ++ ds)).2 := by
    intro b hb y hy r hr
    obtain rfl : ({ g := gb, shared := o } : Border) = b := Option.some.inj (hgb.symm.trans hb)
    have ho' : (_root_.Desc.K14.ended ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).seat k m st).1.2).map
        VerifiableInference.Desc.Third.sharedOfEnd = some o := ho₁
    obtain ⟨e', he', rfl⟩ := Option.map_eq_some_iff.1 ho'
    obtain ⟨-, eo, est', -⟩ := VerifiableInference.Desc.Third.Law.ended_shared _ e' he'
    have hb2 : (VerifiableInference.Desc.Third.sharedOfEnd e').omega = 2 := by
      have q : (sh₃ SF s₀).2.border.map (·.omega) = some 2 := by
        rw [hsh₀]
        exact omega_border_A0
      have q' : (s₀.loc.border.map (borderSh SF s₀.st.codes)).map (·.omega) = some 2 := q
      rw [hb] at q'
      exact Option.some.inj q'
    obtain ⟨x', hx', hsay'⟩ := pO
    have hy' : ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).seat k m st).1.2.st.oracles[2]? = some y := by
      rw [← est', ← hb2]
      exact hy
    obtain rfl : x' = y := Option.some.inj (hx'.symm.trans hy')
    show Says rdE (VerifiableInference.Desc.Third.sharedOfEnd e').st r _
    rw [est']
    exact hsay' r hr
  rw [e₀] at p₀ p₂
  exact say_core (val₁Key Xs L) (thirdPar Xs.chains) hdec hsh₀ hsh₂ _ (valOf (plan₁ (AtPublicFiles.KeyThread.one₀ Xs)) L.R _)
    (fun _ _ _ => rfl) (srow_to ho₀ hsame p₀) (srow_to ho₂ hsame p₂) hOm (hT.2.2.2.1 ds ItemL.rows hiR) he R htie

end

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.say_stand
