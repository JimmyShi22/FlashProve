-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Coin.ReadsKey
import Johnson.Desc.K12.Coin.GameLabelsOwn
import Johnson.Desc.K12.Coin.LawAtTileOwn
/-
Johnson/Desc/K12/Coin/ReadsKeyOwn.lean: THE GAME OF THE PROXIMITY TEST WITH THE KEY, SECOND ARM (the first fold sends its own mask): LeadsK AND KeyLaw AT ANY PIECE THAT HOLDS THE SEAT's ENTRY AS A DESCRIPTION HOLDS IT. Statements and proofs. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING. NO NEW MATHEMATICS: book-keeping on Lean's own definitions.
The first arm: Coin/ReadsKey.lean: its SameCols · sameCols_of_key · qn_reads · ntuple_no · leadsK_of_leads_key · held_sure are CALLED here; Law/HeldKey.lean's keyLaw_of_held too.
WHAT PARTS FROM THE FIRST ARM: the mask's tree is the stretch's own first: its number is base, which lies in no key in front ([lo, base)). BUT «one tuple for all rows» takes of the mask's place the written round alone (GameLabelsOwn.lean's W0_fst): it reads the strings at the MEMBERS' places alone; and these lie in [lo, base): lo ≤ by nlAt's make, < base by the second clause of FirstOpensOwn, WHICH STANDS IN THE CONCLUSION ITSELF (QO).
  clampN lo hi n: n brought into [lo, hi): a device inside one proof: qn_reads asks its range at every place of the book; ntuple_no lets the numbering be turned off the members' places.
  qo_reads: QO reads the strings at the trees lo ≤ j < base alone.
  QVO · qvo_key: the game's relation at a seat is carried by equal keys.
  gameK_pieceO: LeadsK (fun _ => True) … ∧ KeyLaw. gameK_pieceO_le: the same at every greater list of errors (the piece's own errors need only be at least (e, εt), round by round): after the first arm's gameK_piece_le.
  gameK_at_tile₂O_le: AT THE SHARED CHAIN's PIECE NUMBER pre.length OF piecesAt, at whatever errors the family lays there that are at least ours: over tile_pieceOwn₂ (Coin/LawAtTileOwn.lean) and opens_own₂ (Law/OpensOwn.lean): after the first arm's gameK_at_tile₂_le (its le_of_heq is called).
  gameK_at_tile₂O_ride: with what rides of the strings laid beside (the first arm's Rides · strs_ride · allOf_nodup: general in the piece: called). gameK_at_tile₂O_cap: WHERE EVERY PIECE's ERRORS ARE THE CAP (AtCap): no premise on the errors is left: LeadsK, and LeadsBN at every number of slots (LeadsK.bothN), at the piece's own errors. THESE TWO TEXTS WERE MADE OF THE FIRST ARM's OWN (Coin/ReadsKey.lean) BY A PROGRAM THAT TURNS NINE NAMES.
OVER THESE FILES: Coin/FirstBook.lean (ownLabelsB) · GameLabels | GameAlike | GameJ | AtDescOwn and what stands beneath them.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.Pub (johOk batV0 batPriceOk)
open H2K.JointK (keyLaw_of_held opens_own₂)
open Johnson.G.OfPlan (rootsOf)
open scoped ENNReal
open H2K.Pin (NTuple)

/-- n brought into [lo, hi). -/
def clampN (lo hi n : ℕ) : ℕ := max lo (min n (hi - 1))

theorem clampN_range (lo hi n : ℕ) (h : lo < hi) : lo ≤ clampN lo hi n ∧ clampN lo hi n < hi := by
  unfold clampN
  omega

theorem clampN_in (lo hi n : ℕ) (h1 : lo ≤ n) (h2 : n < hi) : clampN lo hi n = n := by
  unfold clampN
  omega

/-- **The second arm's conclusion reads the strings at the trees lo ≤ j < base alone.** -/
theorem qo_reads (F : Frame) (π : P12) (t₁ t₂ ch : ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
    (hfr : 0 < π.nums.free) (t : T12) (y y' : F.E.Str)
    (h : SameCols F (numAt t₁ t₂ ch (.own 0)) (numAt t₁ t₂ ch (.own π.nums.free)) y y')
    (hq : QO F π t₁ t₂ ch rad rd (t, y)) : QO F π t₁ t₂ ch rad rd (t, y') := by
  obtain ⟨hfo, a, rest, G0, Ly, D, hf, hN⟩ := hq
  have hlt : numAt t₁ t₂ ch (.own 0) < numAt t₁ t₂ ch (.own π.nums.free) := by
    show _ + 0 < _ + π.nums.free
    omega
  have hin : ∀ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout)
      (D : H2K.First.Plain), Fixes π t a rest G0 Ly D → ∀ i,
      nuOf π (nlAt π (numAt t₁ t₂ ch (.own 0))) t (D.mems.get i).t =
        clampN (numAt t₁ t₂ ch (.own 0)) (numAt t₁ t₂ ch (.own π.nums.free))
          (nuOf π (nlAt π (numAt t₁ t₂ ch (.own 0))) t (D.mems.get i).t) :=
    fun a rest G0 Ly D hf i => (clampN_in _ _ _ (Nat.le_add_right _ _)
      ((hfo a rest G0 Ly D hf).2.1 i)).symm
  have q1 : QN π (NTuple F π (fun z => clampN (numAt t₁ t₂ ch (.own 0))
      (numAt t₁ t₂ ch (.own π.nums.free)) (nuOf π (nlAt π (numAt t₁ t₂ ch (.own 0))) t z)) rad rd)
      (t, y) :=
    ⟨a, rest, G0, Ly, D, hf, ntuple_no F π _ _ rad rd (t, y) a rest G0 Ly D
      (hin a rest G0 Ly D hf) hN⟩
  obtain ⟨a', rest', G0', Ly', D', hf', hN'⟩ := qn_reads F π _ rad rd _ _
    (fun z => clampN_range _ _ _ hlt) t y y' h q1
  exact ⟨hfo, a', rest', G0', Ly', D', hf', ntuple_no F π _ _ rad rd (t, y') a' rest' G0' Ly' D'
    (fun i => (hin a' rest' G0' Ly' D' hf' i).symm) hN'⟩

/-- The game's relation at a seat, without the clause on the held part. -/
def QVO {P S : Type} (F : Frame) (π : P12) (t₁ t₂ ch : ℕ) (r : Fmt.M1.Stage → ℕ) (rd : ℕ → ℕ)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (a b : (P × S) × F.E.Str) : Prop :=
  ∃ t t', enter a.1.2 = .ok t ∧ leave a.1.2 t' = .ok b.1.2 ∧
    QO F π t₁ t₂ ch (fun s => r s.st) rd (t, a.2)

theorem qvo_key {P S : Type} (F : Frame) (π : P12) (t₁ t₂ ch : ℕ) (r : Fmt.M1.Stage → ℕ)
    (rd : ℕ → ℕ) (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (hfr : 0 < π.nums.free) (hi' : ℕ) (a a' b b' : (P × S) × F.E.Str)
    (ha : (actAt F (Prod.snd : P × S → S) (numAt t₁ t₂ ch (.own 0))
        (numAt t₁ t₂ ch (.own π.nums.free))).2 a =
      (actAt F (Prod.snd : P × S → S) (numAt t₁ t₂ ch (.own 0))
        (numAt t₁ t₂ ch (.own π.nums.free))).2 a')
    (hb : (actAt F (Prod.snd : P × S → S) (numAt t₁ t₂ ch (.own 0)) hi').2 b =
      (actAt F (Prod.snd : P × S → S) (numAt t₁ t₂ ch (.own 0)) hi').2 b')
    (hq : QVO F π t₁ t₂ ch r rd enter leave a b) : QVO F π t₁ t₂ ch r rd enter leave a' b' := by
  obtain ⟨ea, hs⟩ := sameCols_of_key F Prod.snd _ _ a a' ha
  obtain ⟨eb, _⟩ := sameCols_of_key F Prod.snd _ hi' b b' hb
  obtain ⟨t, t', h1, h2, h3⟩ := hq
  have ea' : a.1.2 = a'.1.2 := ea
  have eb' : b.1.2 = b'.1.2 := eb
  refine ⟨t, t', ?_, ?_, qo_reads F π t₁ t₂ ch _ rd hfr t a.2 a'.2 hs h3⟩
  · rw [← ea']
    exact h1
  · rw [← ea', ← eb']
    exact h2

/-- **THE GAME WITH THE KEY, SECOND ARM, at any piece that holds the seat's entry as a
description holds it.** lo: the number of the chain's first own tree. -/
theorem gameK_pieceO (P S Cl' : Type) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (F : Frame) (W : Type) (π : P12) (ch t₁ t₂ : ℕ)
    (rd : ℕ → ℕ) (dB : RDT) (dt : List RDT) (e : ℕ) (εt : Err (uLT (ckP .two) dt))
    (r : Fmt.M1.Stage → ℕ) (p : Piece (ckP .two) F (P × S) Cl' W) (B : Block S Cl')
    (hb : p.b = held B) (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) B)
    (h0 : p.back = []) (hbase : p.base = numAt t₁ t₂ ch (.own π.nums.free))
    (hds : p.ds = dB :: dt) (herr : HEq p.err ((e, εt) : Err (uLT (ckP .two) (dB :: dt))))
    (hA : AtPlaceOwn F π (numAt t₁ t₂ ch) Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st)
      (numAt t₁ t₂ ch (.own π.nums.free)) dB dt εt)
    (hj : johOk π r = true) (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e)
    (hown : π.nums.ownMask = true) (hPl : ownLabelsB π = true)
    (hne : H2K.Made.firstNe π = true) (hfr : 0 < π.nums.free) (lo : ℕ)
    (hlo : numAt t₁ t₂ ch (.own 0) = lo) (ho : ∀ d ∈ p.ds, ∀ j ∈ d.opens, lo ≤ j) :
    p.ior.red.LeadsK (actAt F (Prod.snd : P × S → S) lo p.base).2 (fun _ => True)
        (fun a b => QVO F π t₁ t₂ ch r rd enter leave a b ∧ b.1 = (a.1.1, b.1.2)) p.err ∧
      p.ior.red.KeyLaw (actAt F (Prod.snd : P × S → S) lo p.base).2
        (actAt F (Prod.snd : P × S → S) lo (p.base + p.trees)).2 := by
  subst hlo
  obtain ⟨hP, h1, hlog⟩ := own_pays π (fun s => r s.st) r (fun _ => rfl) hj
    (H2K.Made.batOneOk_of_planOk guardedProximityTestParts π hA.planOk) dB dt hA.like
  have hL := k12_game_alikeVO P S Cl' enter leave F W π t₁ t₂ ch Sg.lstJ Sg.flC Sg.flZ Sg.flZ
    (fun s => r s.st) rd dB dt e (batV0 π r) εt p (by rw [hb]; exact hal.held) h0 hbase hds herr
    hA hP h1 hlog hle hown hPl hne hfr
  have hL' : p.ior.red.Leads (fun _ => True) (QVO F π t₁ t₂ ch r rd enter leave) p.err :=
    hL.conseq (fun _ x => x) fun _ _ _ _ _ hq => hq.1
  have hK := leadsK_of_leads_key p B hb (numAt t₁ t₂ ch (.own 0)) ho _
    (fun a a' b b' ha hb' hq =>
      qvo_key F π t₁ t₂ ch r rd enter leave hfr _ a a' b b' (by rw [← hbase]; exact ha) hb' hq)
    hL'
  exact ⟨hK.beside_sure _ fun a τ b _ hout => held_sure p B hb a b τ hout,
    keyLaw_of_held p B _ hb ho⟩

/-- **The same at every greater list of errors.** -/
theorem gameK_pieceO_le (P S Cl' : Type) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (F : Frame) (W : Type) (π : P12) (ch t₁ t₂ : ℕ)
    (rd : ℕ → ℕ) (dB : RDT) (dt : List RDT) (e : ℕ) (εt : Err (uLT (ckP .two) dt))
    (r : Fmt.M1.Stage → ℕ) (p : Piece (ckP .two) F (P × S) Cl' W) (B : Block S Cl')
    (hb : p.b = held B) (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) B)
    (h0 : p.back = []) (hbase : p.base = numAt t₁ t₂ ch (.own π.nums.free))
    (hds : p.ds = dB :: dt)
    (hε : ∀ ε₀ : Err (uLT (ckP .two) p.ds),
      HEq ε₀ ((e, εt) : Err (uLT (ckP .two) (dB :: dt))) → Err.le ε₀ p.err)
    (hA : AtPlaceOwn F π (numAt t₁ t₂ ch) Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st)
      (numAt t₁ t₂ ch (.own π.nums.free)) dB dt εt)
    (hj : johOk π r = true) (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e)
    (hown : π.nums.ownMask = true) (hPl : ownLabelsB π = true)
    (hne : H2K.Made.firstNe π = true) (hfr : 0 < π.nums.free) (lo : ℕ)
    (hlo : numAt t₁ t₂ ch (.own 0) = lo) (ho : ∀ d ∈ p.ds, ∀ j ∈ d.opens, lo ≤ j) :
    p.ior.red.LeadsK (actAt F (Prod.snd : P × S → S) lo p.base).2 (fun _ => True)
        (fun a b => QVO F π t₁ t₂ ch r rd enter leave a b ∧ b.1 = (a.1.1, b.1.2)) p.err ∧
      p.ior.red.KeyLaw (actAt F (Prod.snd : P × S → S) lo p.base).2
        (actAt F (Prod.snd : P × S → S) lo (p.base + p.trees)).2 := by
  obtain ⟨pb, pbase, pds, pback, pext, perr⟩ := p
  dsimp only at hb h0 hbase hds hε ho
  subst hds
  have h := gameK_pieceO P S Cl' enter leave F W π ch t₁ t₂ rd dB dt e εt r
    (⟨pb, pbase, dB :: dt, pback, pext, (e, εt)⟩ : Piece (ckP .two) F (P × S) Cl' W) B hb hal h0
    hbase rfl HEq.rfl hA hj hle hown hPl hne hfr lo hlo ho
  exact ⟨h.1.mono_err (hε _ HEq.rfl), h.2⟩

/-- **AT THE SHARED CHAIN's PIECE NUMBER pre.length OF `piecesAt`, SECOND ARM**: the game with
the key and the law of keys, WHATEVER the family of extractors and errors lays there, if only its
errors are at least "BAT"'s count times the sampler's number and the place's own errors, round by
round (`herr`); and that pair is below 2⁻¹ ^ k. (A form that pins the family's errors to that pair
would be empty where the family lays the cap: none is typed here.) -/
theorem gameK_at_tile₂O_le {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      VerifiableInference.Desc.Sound.Rest (ckP .two) (VerifiableInference.Desc.Sound.frameAt D (VerifiableInference.Desc.Sound.allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      VerifiableInference.Desc.Sound.Rest (ckP .two) (VerifiableInference.Desc.Sound.frameAt D (VerifiableInference.Desc.Sound.allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      VerifiableInference.Desc.Sound.Rest (ckP .two) (VerifiableInference.Desc.Sound.frameAt D (VerifiableInference.Desc.Sound.allOf D) D.key₃ F.lastChainFirstTreeNumber)
        ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) (π : P12) (r : Fmt.M1.Stage → ℕ) (k : ℕ)
    (enter : F.S₂ → Except String T12) (leave : F.S₂ → T12 → Except String F.S₂)
    (pre : List (Block F.S₂ F.Cl)) (B b' : Block F.S₂ F.Cl) (post : List (Block F.S₂ F.Cl))
    (hfl : F.shared.blocksInOrder = b₂ :: l₂) (hcut : b₂ :: l₂ = pre ++ B :: b' :: post)
    (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) B)
    (hfree : π.nums.free = rootsOf (pre.flatMap (·.rounds)))
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hC : ChainAt π r ((2 : ℝ≥0∞)⁻¹ ^ k)) (hj : johOk π r = true)
    (hbat : batPriceOk π r k = true) (hown : π.nums.ownMask = true)
    (hPl : ownLabelsB π = true) (hne : H2K.Made.firstNe π = true) (hfr : 0 < π.nums.free)
    (rd : ℕ → ℕ)
    (herr : ∀ dB dt, (D.ds₂.drop (pre.flatMap (·.rounds)).length).take
        (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length = dB :: dt →
      Err.le (s := uLT (ckP .two) (dB :: dt))
        (batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt)
        (rest₂ (0 + pre.length) (dB :: dt)).err) :
    ∃ p dB dt,
      ((VerifiableInference.Desc.Sound.piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₂ ::
        (VerifiableInference.Desc.Sound.piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₂)[pre.length]? =
        some p ∧
      p.b = held B ∧
      p.base = D.t₁ + VerifiableInference.Desc.Sound.nTrees (D.ds₂.take (pre.flatMap (·.rounds)).length) ∧ p.ds = dB :: dt ∧
      HEq p.err (rest₂ (0 + pre.length) (dB :: dt)).err ∧
      Err.Below (s := uLT (ckP .two) (dB :: dt))
        (batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) ((2 : ℝ≥0∞)⁻¹ ^ k) ∧
      p.ior.red.LeadsK
        (actAt (VerifiableInference.Desc.Sound.frameAt D (VerifiableInference.Desc.Sound.allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          p.base).2 (fun _ => True)
        (fun a b => QVO (VerifiableInference.Desc.Sound.frameAt D (VerifiableInference.Desc.Sound.allOf D) D.key₂ 0) π F.t₁ F.t₂ 1 r rd enter leave a b ∧
          b.1 = (a.1.1, b.1.2)) p.err ∧
      p.ior.red.KeyLaw
        (actAt (VerifiableInference.Desc.Sound.frameAt D (VerifiableInference.Desc.Sound.allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          p.base).2
        (actAt (VerifiableInference.Desc.Sound.frameAt D (VerifiableInference.Desc.Sound.allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          (p.base + p.trees)).2 := by
  obtain ⟨p, dB, dt, hrow, hpb, hp0, hpbase, hpds, hlist, hperr, hb0, _, hAt, hsm⟩ :=
    tile_pieceOwn₂ F file D h b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd π r k pre B b' post hfl
      hcut hal.rounds hfree hp hC hj hbat hown
  have hho : ∀ x ∈ p.ds, ∀ j ∈ x.opens, F.t₁ ≤ j := by
    intro x hx
    rw [hpds, ← hlist] at hx
    exact opens_own₂ F file D h x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  have hA' : AtPlaceOwn (VerifiableInference.Desc.Sound.frameAt D (VerifiableInference.Desc.Sound.allOf D) D.key₂ 0) π (VerifiableInference.Desc.numAt F.t₁ F.t₂ 1) Sg.lstJ Sg.flC Sg.flZ
      Sg.flZ (fun s => r s.st) (VerifiableInference.Desc.numAt F.t₁ F.t₂ 1 (.own π.nums.free)) dB dt (errJ π r dt) := by
    have e : D.t₁ + VerifiableInference.Desc.Sound.nTrees (D.ds₂.take (pre.flatMap (·.rounds)).length) =
        VerifiableInference.Desc.numAt F.t₁ F.t₂ 1 (.own π.nums.free) := hb0
    rw [← e]
    exact hAt
  have hpe : HEq p.err (rest₂ (0 + pre.length) (dB :: dt)).err :=
    hperr _ fun ds' e => by
      subst e
      exact HEq.rfl
  obtain ⟨hK, hLaw⟩ := gameK_pieceO_le (F.XiPub × F.S₁) F.S₂ F.Cl enter leave _ W π 1 F.t₁ F.t₂ rd
    dB dt _ (errJ π r dt) r p B hpb hal hp0 (hpbase.trans hb0) hpds
    (fun ε₀ h0 => le_of_heq hpds ε₀ p.err _ _ h0 hpe (herr dB dt hlist)) hA' hj (Nat.le_refl _)
    hown hPl hne hfr F.t₁ (by simp [VerifiableInference.Desc.numAt]) hho
  exact ⟨p, dB, dt, hrow, hpb, hpbase, hpds, hpe, hsm, hK, hLaw⟩

/-- **`gameK_at_tile₂O_le` with what rides of the strings laid beside.** -/
theorem gameK_at_tile₂O_ride {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      VerifiableInference.Desc.Sound.Rest (ckP .two) (VerifiableInference.Desc.Sound.frameAt D (VerifiableInference.Desc.Sound.allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      VerifiableInference.Desc.Sound.Rest (ckP .two) (VerifiableInference.Desc.Sound.frameAt D (VerifiableInference.Desc.Sound.allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      VerifiableInference.Desc.Sound.Rest (ckP .two) (VerifiableInference.Desc.Sound.frameAt D (VerifiableInference.Desc.Sound.allOf D) D.key₃ F.lastChainFirstTreeNumber)
        ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) (π : P12) (r : Fmt.M1.Stage → ℕ) (k : ℕ)
    (enter : F.S₂ → Except String T12) (leave : F.S₂ → T12 → Except String F.S₂)
    (pre : List (Block F.S₂ F.Cl)) (B b' : Block F.S₂ F.Cl) (post : List (Block F.S₂ F.Cl))
    (hfl : F.shared.blocksInOrder = b₂ :: l₂) (hcut : b₂ :: l₂ = pre ++ B :: b' :: post)
    (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) B)
    (hfree : π.nums.free = rootsOf (pre.flatMap (·.rounds)))
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hC : ChainAt π r ((2 : ℝ≥0∞)⁻¹ ^ k)) (hj : johOk π r = true)
    (hbat : batPriceOk π r k = true) (hown : π.nums.ownMask = true)
    (hPl : ownLabelsB π = true) (hne : H2K.Made.firstNe π = true) (hfr : 0 < π.nums.free) (rd : ℕ → ℕ)
    (herr : ∀ dB dt, (D.ds₂.drop (pre.flatMap (·.rounds)).length).take
        (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length = dB :: dt →
      Err.le (s := uLT (ckP .two) (dB :: dt))
        (batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt)
        (rest₂ (0 + pre.length) (dB :: dt)).err) :
    ∃ p dB dt,
      ((VerifiableInference.Desc.Sound.piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₂ ::
        (VerifiableInference.Desc.Sound.piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₂)[pre.length]? =
        some p ∧
      p.b = held B ∧
      p.base = D.t₁ + VerifiableInference.Desc.Sound.nTrees (D.ds₂.take (pre.flatMap (·.rounds)).length) ∧ p.ds = dB :: dt ∧
      HEq p.err (rest₂ (0 + pre.length) (dB :: dt)).err ∧
      Err.Below (s := uLT (ckP .two) (dB :: dt))
        (batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) ((2 : ℝ≥0∞)⁻¹ ^ k) ∧
      p.ior.red.LeadsK
        (actAt (VerifiableInference.Desc.Sound.frameAt D (VerifiableInference.Desc.Sound.allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          p.base).2 (fun _ => True)
        (fun a b => (QVO (VerifiableInference.Desc.Sound.frameAt D (VerifiableInference.Desc.Sound.allOf D) D.key₂ 0) π F.t₁ F.t₂ 1 r rd enter leave a b ∧
          b.1 = (a.1.1, b.1.2)) ∧ Rides (VerifiableInference.Desc.Sound.frameAt D (VerifiableInference.Desc.Sound.allOf D) D.key₂ 0) p.base a b) p.err ∧
      p.ior.red.KeyLaw
        (actAt (VerifiableInference.Desc.Sound.frameAt D (VerifiableInference.Desc.Sound.allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          p.base).2
        (actAt (VerifiableInference.Desc.Sound.frameAt D (VerifiableInference.Desc.Sound.allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          (p.base + p.trees)).2 := by
  obtain ⟨p, dB, dt, hrow, hpb, hpbase, hpds, hpe, hsm, hK, hLaw⟩ :=
    gameK_at_tile₂O_le F file D h b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd π r k enter leave pre B
      b' post hfl hcut hal hfree hp hC hj hbat hown hPl hne hfr rd herr
  exact ⟨p, dB, dt, hrow, hpb, hpbase, hpds, hpe, hsm,
    hK.beside_sure _ fun a τ b _ hout => strs_ride p (allOf_nodup D) a b τ hout, hLaw⟩

/-! ## At the letters of record -/

/-- **WHERE EVERY PIECE's ERRORS ARE THE CAP** (`AtCap`, Johnson/Desc/Sound/BoundsAtCap.lean): no
premise on the errors is left: the law with the key, and so the law for a batch at every number of
slots (`LeadsK.bothN`), stand at the piece's own errors, the cap. After the first arm's gameK_at_tile₂_cap. -/
theorem gameK_at_tile₂O_cap {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      VerifiableInference.Desc.Sound.Rest (ckP .two) (VerifiableInference.Desc.Sound.frameAt D (VerifiableInference.Desc.Sound.allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      VerifiableInference.Desc.Sound.Rest (ckP .two) (VerifiableInference.Desc.Sound.frameAt D (VerifiableInference.Desc.Sound.allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      VerifiableInference.Desc.Sound.Rest (ckP .two) (VerifiableInference.Desc.Sound.frameAt D (VerifiableInference.Desc.Sound.allOf D) D.key₃ F.lastChainFirstTreeNumber)
        ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) (π : P12) (r : Fmt.M1.Stage → ℕ)
    (enter : F.S₂ → Except String T12) (leave : F.S₂ → T12 → Except String F.S₂)
    (pre : List (Block F.S₂ F.Cl)) (B b' : Block F.S₂ F.Cl) (post : List (Block F.S₂ F.Cl))
    (hfl : F.shared.blocksInOrder = b₂ :: l₂) (hcut : b₂ :: l₂ = pre ++ B :: b' :: post)
    (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) B)
    (hfree : π.nums.free = rootsOf (pre.flatMap (·.rounds)))
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hC : ChainAt π r ((2 : ℝ≥0∞)⁻¹ ^ 128)) (hj : johOk π r = true)
    (hbat : batPriceOk π r 128 = true) (hown : π.nums.ownMask = true)
    (hPl : ownLabelsB π = true) (hne : H2K.Made.firstNe π = true) (hfr : 0 < π.nums.free) (rd : ℕ → ℕ) (hcap : AtCap rest₂)
    (N : ℕ) :
    ∃ p,
      ((VerifiableInference.Desc.Sound.piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₂ ::
        (VerifiableInference.Desc.Sound.piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₂)[pre.length]? =
        some p ∧
      p.b = held B ∧
      p.base = D.t₁ + VerifiableInference.Desc.Sound.nTrees (D.ds₂.take (pre.flatMap (·.rounds)).length) ∧
      p.ior.red.LeadsK
        (actAt (VerifiableInference.Desc.Sound.frameAt D (VerifiableInference.Desc.Sound.allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          p.base).2 (fun _ => True)
        (fun a b => (QVO (VerifiableInference.Desc.Sound.frameAt D (VerifiableInference.Desc.Sound.allOf D) D.key₂ 0) π F.t₁ F.t₂ 1 r rd enter leave a b ∧
          b.1 = (a.1.1, b.1.2)) ∧ Rides (VerifiableInference.Desc.Sound.frameAt D (VerifiableInference.Desc.Sound.allOf D) D.key₂ 0) p.base a b) p.err ∧
      p.ior.red.LeadsBN
        (actAt (VerifiableInference.Desc.Sound.frameAt D (VerifiableInference.Desc.Sound.allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          p.base).2 (fun _ => True)
        (fun a b => (QVO (VerifiableInference.Desc.Sound.frameAt D (VerifiableInference.Desc.Sound.allOf D) D.key₂ 0) π F.t₁ F.t₂ 1 r rd enter leave a b ∧
          b.1 = (a.1.1, b.1.2)) ∧ Rides (VerifiableInference.Desc.Sound.frameAt D (VerifiableInference.Desc.Sound.allOf D) D.key₂ 0) p.base a b) N p.err ∧
      p.ior.red.KeyLaw
        (actAt (VerifiableInference.Desc.Sound.frameAt D (VerifiableInference.Desc.Sound.allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          p.base).2
        (actAt (VerifiableInference.Desc.Sound.frameAt D (VerifiableInference.Desc.Sound.allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          (p.base + p.trees)).2 := by
  obtain ⟨p, dB, dt, hrow, hpb, hpbase, _, _, _, hK, hLaw⟩ :=
    gameK_at_tile₂O_ride F file D h b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd π r 128 enter leave
      pre B b' post hfl hcut hal hfree hp hC hj hbat hown hPl hne hfr rd fun dB dt hc => by
        obtain ⟨dB', dt', hc', _, hsm⟩ := atPlaceOwn_tile₂ F file D h D.key₂ 0 π r 128 pre B
          (b' :: post) (hfl.trans hcut) hal.rounds hfree hp hC hj hbat hown
        obtain ⟨rfl, rfl⟩ := List.cons.inj (hc.symm.trans hc')
        rw [hcap (0 + pre.length) (dB :: dt)]
        exact Err.le_cap_of_below_inv 128 _ hsm
  exact ⟨p, hrow, hpb, hpbase, hK, hK.bothN N, hLaw⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.qo_reads
#print axioms VerifiableInference.Desc.K12.Coin.qvo_key
#print axioms VerifiableInference.Desc.K12.Coin.gameK_pieceO
#print axioms VerifiableInference.Desc.K12.Coin.gameK_pieceO_le
#print axioms VerifiableInference.Desc.K12.Coin.gameK_at_tile₂O_le
#print axioms VerifiableInference.Desc.K12.Coin.gameK_at_tile₂O_ride
#print axioms VerifiableInference.Desc.K12.Coin.gameK_at_tile₂O_cap
