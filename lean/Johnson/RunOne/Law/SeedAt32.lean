-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/SeedAt32.lean: THEOREMS. THE VERIFIER's STATE ALONG THE KEY FILE's
LAST CHAIN, OFF THE HISTORY, IN THE GOALS' SCOPE: its codes; the sending kind's row at an OOD seed (K1.SeedIs) at the index masks' message and
(with every coordinate of the seed canonical: SeedOk) at W's; AND A CARRYING FOR OMEGA's COPY: at_32 GIVES TWO OF THE THREE OOD SEEDS AND
CARRIES THE THIRD ⇐ hΩ, A PREMISE ON THE HANDED SHARED CHAIN's LAST STATE; it is paid by
omega_end, and at_32' is at_32 without it (Johnson/RunOne/Law/SeedAt32Paid.lean), under three
further premises: hL (the later places are made of the same m), hw (`wantedOk`) and hfit (the
instance's key fits the fold's index); who pays hfit is not said there.

Words: "the last chain" is chain 3 of Key.descriptionFromSource X N P; a "border" k lies in front of sub-protocol k of a chain; "handed" is what a later
chain's public part holds of an earlier chain's last state; "Omega's copy" is the message that K14's second part lays into the last chain's
statement.

Main names:
  codes_3            the state's codes are the written key's, at every border.
  seedIs_idx_3       K1.SeedIs at message 0 (the index masks), at every border.
  seedOk_w_3         SeedOk (Johnson/RunOne/KeySeedOk.lean) at W's message, number wAt, at every border. SeedOk.seedIs gives K1.SeedIs.
  omega_carried      NO PREMISE ON THE PLAN. From border 1 on: K1.SeedIs at the handed shared state, at Omega's number there, gives
                     K1.SeedIs at the state, at the copy's number (the number of messages at the handed first chain's end): same OOD seed
                     and answer. Over ToldDesc.seedIs_copy and laid_k14Second.
  msgs_19            in scope the first chain's end holds wAt + 2 messages.
  seedIs_omega_3     omega_carried at the written shape and the number wAt + 2 ⇐ hΩ.
  at_32              at border 2, in the proximity test's files' letters ⇐ hΩ and hw₃ (a clause of the border's invariant).
The constants by their full names: SeedIs is VerifiableInference.Desc.K1.SeedIs (Johnson/Desc/K1/Law/SeedIs.lean); SeedOk is
Johnson.RunOne.KeyMsg.SeedOk (Johnson/RunOne/KeySeedOk.lean); OpenKinds is OnBytes.Means.OpenKinds (Johnson/Desc/Means/Holds.lean); nOwn is
Johnson.RunOne.KeyRows23.nOwn; plan₁ and wAt are Johnson.RunOne.KeyRows1's.
Kin: idx_seedIs and w_seedIs (Johnson/RunOne/KeyMsgAll.lean) have K1.SeedIs at message 0 and at W's
message at the first chain's states behind their sendings, under their premises (the port's
condition test among them); they are not called here. seedIs_idx_3 says the like at the last chain's
states; seedOk_w_3 says more (SeedOk), which the proximity test's files ask at W.


IS IT EMPTY? codes_3 · seedIs_idx_3 · seedOk_w_3 speak at every state that the last chain reaches; the scope's premises are shown together of
nothing here. seedIs_omega_3 and at_32 ARE EMPTY UNTIL hΩ IS PAID. That an honest key file reaches any border of the last chain is not shown
here.
What is not claimed. hΩ. Which OOD seed. Of W's seed: of ONE seed (an ∃), not of every seed whose form is the stored row. Nothing for Omega at
border 0. One size. Nothing on soundness.

-/
import Johnson.RunOne.Law.BookAt32
import Johnson.Loose.ToldDesc.SeedCarried
import Johnson.Desc.Third.Law.Laid
import Johnson.RunOne.KeySeedOk
import Johnson.RunOne.KeyMsgAll
import Johnson.RunOne.KeyCodesScope
import Johnson.RunOne.KeyWalkAny
import Johnson.Top.Fire.Code.Row117Nine
import Johnson.Top.Fire.Code.Row30AtName

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.SeedAt32
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key (FirstState Claim Xi Lookup)
open VerifiableInference.Desc.K1 (SeedIs SmpStay groundKeeps_smpStay condPort shapesOf shapeAt sampledAt)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Key.Fill (six)
open Johnson.Top.H (csKey shIdx)
open Johnson.RunOne.KeyRows1 (plan₁ wAt)
open Johnson.RunOne.KeyRows23 (Fk oneAt St₂ St₃ nOwn atSix)
open Johnson.RunOne.KeySendGood (parW cond_of planOwn_w asks_in_scope rounds_w samples_of_ranges)
open Johnson.RunOne.KeyLetters (codes_full idx_shape_full)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope)
open Johnson.RunOne.Law.BookAt32 (back_one seal_19)
open Lk6.AtPlan (keyFull)
open LPFD (Hist₁ Hist₂ Hist₃ Reached)

abbrev i0 : Fin six.length := ⟨0, by decide⟩
abbrev i2 : Fin six.length := ⟨2, by decide⟩
abbrev i4 : Fin six.length := ⟨4, by decide⟩

variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-! ## 1 Omega's copy: a carrying, with no premise on the plan -/

/-- **From border 1 on: what held of Omega at the handed shared chain's last state holds of Omega's copy**: the same OOD seed, the same OOD
answer. The copy's number is the number of messages at the handed first chain's end. (The law beneath asks that the state in front of K14's
second part has the codes cs: the last chain's start tests that the two earlier chains' codes are one, so the premise's own first clause
pays it.) -/
theorem omega_carried (D : WholeD) (j : ℕ) (a : (Xi × FirstState × St₂) × St₃) (h : Hist₃ (Fk X N P) D (1 + j) a)
    {cs : Codes} {sh : OracleShape} {ρ} {y}
    (hΩ : SeedIs cs sh a.1.2.2.st a.1.2.2.loc.oOmega ρ y) :
    SeedIs cs sh a.2.st a.1.2.1.d.st.oracles.size ρ y := by
  obtain ⟨x1, h1, e1, hs⟩ := Johnson.RunOne.KeyWalk.hist₃_rel groundKeeps_smpStay Johnson.RunOne.KeyWalk.begin_smp D 1 j a h
  obtain ⟨f, hfl, -, -, hfd⟩ := Johnson.RunOne.KeyRows23.second_flat X N P
  obtain ⟨a₀, b₀, rs₀, cols₀, hr₀, hb₀, hd₀, -⟩ := Reached.last (k := 0) h1
  have hfl' : (Fk X N P).second.blocksInOrder = [f, Johnson.RunOne.KeyRows23.seat (Third.takenSources (ownTest P)),
               Johnson.RunOne.KeyRows23.seat (Johnson.RunOne.KeyRows23.own₃ P), Johnson.RunOne.KeyRows23.seat (Johnson.RunOne.KeyRows23.end₃At X P)] := hfl
  rw [hfl'] at hb₀
  have q₀ : b₀ = (held f : Block ((Xi × FirstState × St₂) × St₃) Key.Claim) := (Option.some.inj hb₀).symm
  rw [q₀] at hd₀
  obtain ⟨e₀, d₀⟩ := held_decide f a₀ _ _ x1 hd₀
  obtain ⟨-, hst⟩ : Hist₂ (Fk X N P) D (Fk X N P).shared.blocksInOrder.length ((a₀.1.1, a₀.1.2.1), a₀.1.2.2) ∧
      ((Fk X N P).start₃ a₀.1.1 a₀.1.2.1 a₀.1.2.2).toOption = some a₀.2 := hr₀
  obtain ⟨o, l, -, ⟨ho1, -, -, ho4⟩, hs3⟩ :=
    Johnson.RunOne.KeyRows23.starts_fkD X N P a₀.1.1 a₀.1.2.1 a₀.1.2.2 a₀.2 (LPFD.ok_of_toOption hst)
  rw [hfd] at d₀
  obtain ⟨b, yO, G, dot, L⟩ := Third.Law.laid_k14Second (Cl := Unit) (thirdPar X.chains) a₀.2 x1.2 _ _ d₀
  obtain ⟨fo, -, hst3⟩ := Third.Law.start₃E_inv _ _ _ _ _ _ _ _ _ _ _ hs3
  obtain ⟨hc1, hc2, e0⟩ := Third.Law.start₃_inv _ _ _ _ hst3
  have hb : b.shared = o := by
    have hbo := L.border
    rw [e0] at hbo
    exact (congrArg (·.shared) (Option.some.inj hbo)).symm
  have est : a₀.2.st = a₀.1.2.1.d.st := Third.Law.start₃E_st _ _ _ _ _ _ _ _ _ _ _ hs3
  have ea : a₀.1 = a.1 := e₀.symm.trans e1
  rw [← ea] at hΩ ⊢
  have hΩ' : SeedIs cs sh b.shared.st b.shared.omega ρ y := by
    rw [hb, ho1, ho4]
    exact hΩ
  have hcs : a₀.2.st.codes = cs := by
    have h2 : o.st.codes = cs := by
      rw [← hb]
      exact hΩ'.1
    rw [e0]
    show fo.st.codes = cs
    rw [hc1, ← hc2]
    exact h2
  have hc := ToldDesc.seedIs_copy L hcs hΩ'
  rw [est] at hc
  exact hc.stays hs

/-! ## 2 In scope: the codes; the index masks' message; W's message -/

section
variable {Zp : VerifierAndGoals.PublicFiles} {Z : OnBytes.Model.Verify.Public} {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}

/-- **The state's codes are the written key's**, at every border of the last chain. -/
theorem codes_3 (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol Z) (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (D : WholeD) (k : ℕ) (a : (Xi × FirstState × St₂) × St₃) (h : Hist₃ (Fk X N P) D k a) : a.2.st.codes = csKey :=
  (Johnson.RunOne.KeyCodes.codes_in_scope₃ hZ hP hm hX D k a h).trans codes_full

theorem flat_19 (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol Z) (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (Fk X N P).planOk = true) : (Fk X N P).first.blocksInOrder.length = 19 := by
  obtain ⟨x₀, x₁, hl⟩ := LPFD.hl_in_scope hZ hP hm hX hp
  obtain ⟨bw, hbw⟩ := LPFD.hw_in_scope hZ hP hm hX hp pieces (LPFD.sent17 X) (LPFD.g17 X)
  exact Johnson.RunOne.KeyRows1.flat_length (oneAt X) X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl bw hbw

/-- **The index masks' message holds the sending kind's row at an OOD seed**, at every border of the last chain. -/
theorem seedIs_idx_3 (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol Z) (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (Fk X N P).planOk = true) (D : WholeD) (k : ℕ) (a : (Xi × FirstState × St₂) × St₃) (h : Hist₃ (Fk X N P) D k a) :
    ∃ ρ y, SeedIs csKey (six.get i0).1 a.2.st 0 ρ y := by
  obtain ⟨-, -, -, hi, hc⟩ := five_in_scope hZ hP hm hX hp
  obtain ⟨x0, h0, -, hs⟩ := Johnson.RunOne.KeyWalk.seedIs_into D 1 18 (by rw [flat_19 hZ hP hm hX hp]) k a h
  obtain ⟨ρ, y, hy⟩ := Johnson.RunOne.KeyMsg.idx_seedIs_at (cs := csKey) (sh := shIdx) (hc.trans codes_full)
    (by rw [hi]; exact idx_shape_full) _ (Johnson.RunOne.KeyMsg.cond_idx_plan hp hc hi) (by decide) D 0 x0 h0
  exact ⟨ρ, y, hs _ _ _ _ _ hy⟩

/-- SeedOk along equations of its letters. -/
theorem seedOk_cast {cs cs' : Codes} {s s' : OracleShape} {St : Statement} {o o' : ℕ} (hc : cs = cs') (hs : s = s') (ho : o = o')
    (h : ∃ ρ y, Johnson.RunOne.KeyMsg.SeedOk cs s St o ρ y) : ∃ ρ y, Johnson.RunOne.KeyMsg.SeedOk cs' s' St o' ρ y := by
  subst hc hs ho
  exact h

/-- **W's message holds the sending kind's row at an OOD seed whose coordinates are canonical**, at every border of the last chain. -/
theorem seedOk_w_3 (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol Z) (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (Fk X N P).planOk = true) (hN : rangesNumbers m = .ok N) (D : WholeD) (k : ℕ) (a : (Xi × FirstState × St₂) × St₃)
    (h : Hist₃ (Fk X N P) D k a) : ∃ ρ y, Johnson.RunOne.KeyMsg.SeedOk csKey (six.get i2).1 a.2.st (wAt (oneAt X)) ρ y := by
  obtain ⟨x₀, x₁, hl⟩ := LPFD.hl_in_scope hZ hP hm hX hp
  obtain ⟨bw, hbw⟩ := LPFD.hw_in_scope hZ hP hm hX hp pieces (LPFD.sent17 X) (LPFD.g17 X)
  obtain ⟨c₁, k₁, q₁⟩ : ∃ c₁ k₁, (Fk X N P).first.blocksInOrder = c₁ :: k₁ := ⟨_, _, rfl⟩
  have h5s := five_in_scope hZ hP hm hX hp
  have hlen := flat_19 hZ hP hm hX hp
  obtain ⟨⟨Pb⟩, -⟩ := LPFD.public117_full (oneAt X) pieces (LPFD.g17 X) h5s.2.1 h5s.2.2.1 h5s.2.2.2.2
    (samples_of_ranges hp h5s.2.1) (fun _ hm' => planOwn_w hp hm')
  have A := (asks_in_scope hZ hP hm hX hp).2.2 #[Pb.n₁, Pb.n₂] Pb.two
  have hC : condPort (parW X #[Pb.n₁, Pb.n₂]) (fun _ => 3138896) = true :=
    cond_of _ _ (planOwn_w hp Pb.two) (LPFD.lengths_key hZ hP hm hX hp) A.meets
  have hsh : shapesOf (parW X #[Pb.n₁, Pb.n₂]) = [Pb.n₁.shape, Pb.n₂.shape] := by
    unfold parW
    rw [Johnson.RunOne.KeyMsg.shapes_of]
    rfl
  have h0 : 0 < (shapesOf (parW X #[Pb.n₁, Pb.n₂])).length := by rw [hsh]; exact Nat.succ_pos _
  have hat : shapeAt (parW X #[Pb.n₁, Pb.n₂]) ⟨0, h0⟩ = Pb.n₁.shape := by
    show (shapesOf (parW X #[Pb.n₁, Pb.n₂]))[0] = _
    simp [hsh]
  have hk' : sampledAt (parW X #[Pb.n₁, Pb.n₂]) ⟨0, h0⟩ := by
    show (shapesOf (parW X #[Pb.n₁, Pb.n₂]))[0].answers ≠ 0
    have e : (shapesOf (parW X #[Pb.n₁, Pb.n₂]))[0] = Pb.n₁.shape := hat
    rw [e]
    exact Pb.sampled
  obtain ⟨x1, h1, -, hs⟩ := Johnson.RunOne.KeyWalk.hist₃_from_border_rel groundKeeps_smpStay Johnson.RunOne.KeyWalk.begin_smp D 18 1
    (by rw [hlen]) k a h
  obtain ⟨b17, hb17⟩ : ∃ b, (Fk X N P).first.blocksInOrder[17]? = some b := ⟨_, List.getElem?_eq_getElem (by rw [hlen]; decide)⟩
  obtain rfl := LPFD.block17 X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl bw hbw b17 hb17
  obtain ⟨x0, hx0, -, ρ, y, hy⟩ := Johnson.RunOne.KeyMsg.send_seedOk (parW X #[Pb.n₁, Pb.n₂]) _ hC _ 17 hb17 (rounds_w Pb.two hbw)
    (Johnson.RunOne.KeyMsg.w_named Pb.two hbw) ⟨0, h0⟩ hk' D x1 h1
  have A17 := LPFD.aSide_at_all X N P c₁ k₁ D q₁ hZ hP hm hX hp (firstTree_of_rangesNumbers hN) 17 x0 (by decide) hx0
  have n17 : (show FirstState from x0.2).d.st.oracles.size = wAt (oneAt X) := (Johnson.RunOne.KeyRows1.front17 (oneAt X) x0.2 A17.1).1
  exact seedOk_cast (LPFD.codes_key hZ hP hm hX hp) (hat.trans (LPFD.shapeW_scope X h5s.2.2.1 Pb)) (by rw [n17]; rfl) ⟨ρ, y, hy.stays hs⟩

/-! ## 3 Omega's copy at the written shape ⇐ hΩ; border 2 in the proximity test's files' letters -/

/-- **In scope the first chain's end holds wAt + 2 messages.** -/
theorem msgs_19 (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol Z) (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (Fk X N P).planOk = true) (hN : rangesNumbers m = .ok N) (D : WholeD) (a : Xi × FirstState) (h : Hist₁ (Fk X N P) D 19 a) :
    a.2.d.st.oracles.size = wAt (oneAt X) + 2 := by
  obtain ⟨x₀, x₁, hl⟩ := LPFD.hl_in_scope hZ hP hm hX hp
  obtain ⟨bw, hbw⟩ := LPFD.hw_in_scope hZ hP hm hX hp pieces (LPFD.sent17 X) (LPFD.g17 X)
  obtain ⟨c₁, k₁, q₁⟩ : ∃ c₁ k₁, (Fk X N P).first.blocksInOrder = c₁ :: k₁ := ⟨_, _, rfl⟩
  have h5s := five_in_scope hZ hP hm hX hp
  obtain ⟨⟨Pb⟩, -⟩ := LPFD.public117_full (oneAt X) pieces (LPFD.g17 X) h5s.2.1 h5s.2.2.1 h5s.2.2.2.2
    (samples_of_ranges hp h5s.2.1) (fun _ hm' => planOwn_w hp hm')
  have h18 := seal_19 hl hbw D a h
  obtain ⟨a17, b, rs, gs, h17, hb, -, hd, hf⟩ := back_one D 17 a h18
  have eb := LPFD.block17 X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl bw hbw b hb
  have A17 := LPFD.aSide_at_all X N P c₁ k₁ D q₁ hZ hP hm hX hp (firstTree_of_rangesNumbers hN) 17 a17 (by decide) h17
  exact Johnson.RunOne.KeyRows1.sizeW_of_yes (oneAt X) pieces (LPFD.sent17 X) (LPFD.g17 X) Pb bw hbw b (by rw [eb]; rfl)
    (by rw [eb]; exact rounds_w Pb.two hbw) a17.2 a.2 rs gs hf hd A17.1 A17.2.2.1

/-- **Omega's copy, at the written shape and its number ⇐ hΩ.** (`seedIs_omega_3'`, SeedAt32Paid.lean, calls this.) hΩ: K1.SeedIs at the HANDED shared chain's last state, at Omega's number
there: A PREMISE THAT IS NOT PAID HERE: until it is, this is a carrying and no fact. -/
theorem seedIs_omega_3 (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol Z) (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (Fk X N P).planOk = true) (hN : rangesNumbers m = .ok N) (D : WholeD) (j : ℕ) (a : (Xi × FirstState × St₂) × St₃)
    (h : Hist₃ (Fk X N P) D (1 + j) a) (hΩ : ∃ ρ y, SeedIs csKey (six.get i4).1 a.1.2.2.st a.1.2.2.loc.oOmega ρ y) :
    ∃ ρ y, SeedIs csKey (six.get i4).1 a.2.st (wAt (oneAt X) + 2) ρ y := by
  obtain ⟨ρ, y, hy⟩ := hΩ
  have h19 : Hist₁ (Fk X N P) D 19 (a.1.1, a.1.2.1) :=
    flat_19 hZ hP hm hX hp ▸ LPFD.hist₂_handed (Fk X N P) D _ _ (LPFD.hist₃_handed (Fk X N P) D _ a h)
  have e : a.1.2.1.d.st.oracles.size = wAt (oneAt X) + 2 := msgs_19 hZ hP hm hX hp hN D _ h19
  have hc := omega_carried D j a h hy
  rw [e] at hc
  exact ⟨ρ, y, hc⟩

/-- **Border 2 of the last chain, in the proximity test's files' letters ⇐ hΩ · hw₃.** TWO OF THE THREE OOD SEEDS ARE GIVEN; THE THIRD IS
CARRIED FROM hΩ (see seedIs_omega_3). hw₃: a clause of the border's invariant (shapeB₃). -/
theorem at_32 (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol Z) (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (Fk X N P).planOk = true) (hN : rangesNumbers m = .ok N) (D : WholeD) (a : (Xi × FirstState × St₂) × St₃)
    (h : Hist₃ (Fk X N P) D 2 a) (hw₃ : (plan₁ (oneAt X)).orc 2 = some a.2.loc.w)
    (hΩ : ∃ ρ y, SeedIs csKey (six.get i4).1 a.1.2.2.st a.1.2.2.loc.oOmega ρ y) :
    a.2.st.codes = csKey ∧
      (∀ oI, (plan₁ (oneAt X)).orc 0 = some oI → (∃ ρ yv, SeedIs csKey (six.get i0).1 a.2.st oI ρ yv) ∧ oI ≠ nOwn a.2) ∧
      (∃ ρ yv, Johnson.RunOne.KeyMsg.SeedOk csKey (six.get i2).1 a.2.st a.2.loc.w ρ yv) ∧
      (∃ ρ yv, SeedIs csKey (six.get i4).1 a.2.st (nOwn a.2) ρ yv) ∧
      (plan₁ (oneAt X)).num a.2.loc.w = some 2 ∧ Means.OpenKinds a.2.st := by
  have hw' : some (wAt (oneAt X)) = some a.2.loc.w := hw₃
  have ew : a.2.loc.w = wAt (oneAt X) := (Option.some.inj hw').symm
  have en : nOwn a.2 = wAt (oneAt X) + 2 := by
    unfold nOwn
    rw [ew]
  have h5s := five_in_scope hZ hP hm hX hp
  refine ⟨codes_3 hZ hP hm hX D 2 a h, fun oI hI => ?_, ?_, ?_, ?_, ?_⟩
  · have hI' : some 0 = some oI := hI
    obtain rfl := Option.some.inj hI'
    exact ⟨seedIs_idx_3 hZ hP hm hX hp D 2 a h, by rw [en]; omega⟩
  · rw [ew]
    exact seedOk_w_3 hZ hP hm hX hp hN D 2 a h
  · rw [en]
    exact seedIs_omega_3 hZ hP hm hX hp hN D 1 a h hΩ
  · exact LPFD.num_at_w (oneAt X) (by rw [h5s.2.1]; exact Johnson.RunOne.KeyLetters.hst_full) _ hw₃
  · exact Johnson.RunOne.KeyWalk.openKinds_at_reached₃ D 2 a h

end

end Johnson.RunOne.Law.SeedAt32

#print axioms Johnson.RunOne.Law.SeedAt32.omega_carried
#print axioms Johnson.RunOne.Law.SeedAt32.codes_3
#print axioms Johnson.RunOne.Law.SeedAt32.flat_19
#print axioms Johnson.RunOne.Law.SeedAt32.seedIs_idx_3
#print axioms Johnson.RunOne.Law.SeedAt32.seedOk_cast
#print axioms Johnson.RunOne.Law.SeedAt32.seedOk_w_3
#print axioms Johnson.RunOne.Law.SeedAt32.msgs_19
#print axioms Johnson.RunOne.Law.SeedAt32.seedIs_omega_3
#print axioms Johnson.RunOne.Law.SeedAt32.at_32
