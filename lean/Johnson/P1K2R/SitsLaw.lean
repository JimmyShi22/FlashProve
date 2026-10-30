-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/SitsLaw.lean (over
SitsStep.lean and Johnson/Top/H0/K2Caller/SeatedAt.lean | NumsAt.lean | SitsLaw.lean): THE ROW
«K02_sits» AND THE KIND's LAW IN ONE SENTENCE: at each of the 25 places of the code switch in the
proof file's written description, the law of the code switch holds of the piece at the SEATED
block, read through its door, at the typed record that is made of the planner's own record of
that place's group, under the law's own premises, each by name. NO BLOCK IMPORTS THIS FILE.
  k2P_p2At            the lot's own numbers at a place (IM.k2P Z a nm st n, n by numsAt) meet P2At
                      at the typed record rowOf P.z lo l kept f, f := P.frames[the link, or behind
                      the links the number of links], whatever lo, l and kept are: numsAt's eight
                      formulas are p2At_frame's eight equations, each by rfl. With it: n.codes and
                      n.sent are the planner's, and layTrees lays them
  k02_leads_of_sits   the law at a seated block (k2_leads_seated), called with «Sits B (K2.codeSwitchKind p)
                      enter leave»
  LawAt Z G a nm b    the numbers n · the planner's record f · a word «stands» · a door · Sits b
                      (K2.codeSwitchKind p) enter leave · ∀ lo l kept, K02LawOf (rowOf P.z lo l kept f) p b
                      enter leave
  lawAt_of · lawAt_of_sitsAt · lawAt_of_sitsJoined · lawAt_of_sitsFramed   from SitsAt |
                                                                           SitsJoined | SitsFramed
                                                                           (SitsStep.lean) to
                                                                           LawAt
  k02_sits_law        in the goals' scope, at onlineDescription's value: at all 25 places: where the seated
                      block's test on the plan says yes: LawAt
  DoorLaw · LawArms · LawJoined · k02_sits_law_named   THE SAME WITH THE DOORS BY NAME: SitsAt's |
                                                       SitsJoined's arms kept, each with its
                                                       K02LawOf at that very «stands» and door; at
                                                       a link the door out is leaveOpened fr, fr
                                                       the link's own row of framesOf: this is the
                                                       sentence to read alone; LawAt, with «there
                                                       is a door», is weaker
  LawArmsFramed · lawArms_of_sitsFramed   the elder form at a link: kept for whoever calls it
LIMITS. THE LAW's OWN PREMISES STAY PREMISES, inside K02LawOf, to the letter: r.ok · r.writtenOK ·
the letters X, iJ, iQ · written rounds with the block's entries and kinds · hon · hpr · LawAfter ·
Rides · FrontNums: nothing here pays one of them, and no member is shown: where they cannot be met
together the sentence is idle. The lists lo, l, kept are free in LawAt; the test r.ok inside
K02LawOf holds them against the planner's group and samples in its own clauses; that they ARE the
planner's lists is not said. By Sits' definition nothing forbids a door that forgets: so read
k02_sits_law_named, which names the doors. THE LEVEL IS A FIELD, NOT A NUMBER: 2⁻¹ ^ r.set.target
with r.set = P.z.set: that the target is 128 in scope is not said here: owed (at the written
records K2Caller/At128.lean says it: target_full; the equation of the plan's record with a
written one is what lacks). What the door's two halves keep of what the law reads is not said
here. The limits of Sits.lean and SitsStep.lean. No soundness is claimed.

-/
import Johnson.P1K2R.SitsStep
import Johnson.Top.H0.K2Caller.SeatedAt
import Johnson.Top.H0.K2Caller.NumsAt
import Johnson.Top.H0.K2Caller.SitsLaw

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2

open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim Place)
open VerifiableInference.Desc.Sound (Frame Piece below)
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K2Hands
open VerifiableInference.Desc.First.K2Caller
open H2K.JointK (Sits)
open _root_.Run (ckP)
open scoped ENNReal

theorem k2P_p2At {P : Prep} {Z : ProofFile.Pub} {a : VerifiableInference.Desc.Place}
    {nm : String} {st : K2.At} {n : Nums} (hn : numsAt P a.link = some n) :
    ∃ (f : FrameN) (lay : TreeLay),
      P.frames[a.link.getD P.z.request.link.length]? = some f ∧
      layTrees P.z.codes f.sent.toArray = some lay ∧
      n.codes = P.z.codes ∧ n.sent = f.sent.toArray ∧
      ∀ (lo l : List (OracleShape × ℕ)) (kept : List ℕ),
        P2At (rowOf P.z lo l kept f) (IM.k2P Z a nm st n) := by
  unfold numsAt at hn
  simp only [Option.bind_eq_bind, Option.pure_def] at hn
  split at hn
  · cases hn
  · obtain ⟨_, _, hn⟩ := Option.bind_eq_some_iff.1 hn
    obtain ⟨f, hf, hn⟩ := Option.bind_eq_some_iff.1 hn
    obtain ⟨lay, hl, hn⟩ := Option.bind_eq_some_iff.1 hn
    obtain ⟨read, _, hn⟩ := Option.bind_eq_some_iff.1 hn
    cases hn
    exact ⟨f, lay, hf, hl, rfl, rfl, fun lo l kept =>
      p2At_frame P.z f lo l kept lay hl _ rfl rfl rfl rfl rfl rfl rfl rfl⟩

set_option maxHeartbeats 2000000 in
theorem k02_leads_of_sits {F : Frame} {W W' Cl : Type} {r : SwRow} (h : r.ok = true)
    (hW : r.writtenOK = true) (X : Letters r (r.ok_says h))
    (iJ : ((rowsAt r (r.ok_says h) X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r (r.ok_says h) X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    (d₁ d₂ : RDT) (ρ : WordsOf (selZ X iJ iQ) d₁) (w : K2Wr r d₁ d₂) (p : K2.P2) (base : ℕ)
    (ext : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → W → W)
    (strs : Rec × F.E.Str → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).Ex.Str)
    (inX : Rec → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).X) (on : Rec × F.E.Str → Prop)
    (hon : ∀ a, on a → (Cb.Pv.SendLocRide.inJ (selZ X iJ iQ)).on (lawFa X iJ iQ strs inX a))
    (hpr : ∀ a, on a → ((Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).S.over
      (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).A).on (lawFa X iJ iQ strs inX a))
    (hA : LawAfter X iJ iQ d₁ d₂ ρ p strs inX (shownP X iJ iQ d₁ d₂ ρ p base ext) on)
    (n0 : ℕ) (b₀ : TB X iJ iQ) (oldB : Rec × F.E.Str → (selZ X iJ iQ).sw.S₀.Smp)
    (strB : Rec × F.E.Str → (selLoc X iJ iQ).S.ext.Str)
    (carB : Rec × F.E.Str → X.St₀ × X.E₀.Str)
    (hR : Rides (W := W) X iJ iQ d₁ d₂ ρ p base ext strs inX on oldB strB carB)
    (hN : FrontNums (F := F) (r := r) p n0 on)
    (B : Block Rec Cl) (enter : Rec → Except String Rec) (leave : Rec → Rec → Except String Rec)
    (hX : Sits B (K2.codeSwitchKind (Cl := Unit) p) enter leave)
    (ext' : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → W' → W') :
    (seatedAt (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext) B ext').ior.red.Leads
      (fun a => ∃ t, enter a.1 = .ok t ∧ on (t, a.2))
      (fun a a' => ∃ t t', enter a.1 = .ok t ∧ leave a.1 t' = .ok a'.1 ∧
        K2Q X iJ iQ p strs inX (fbOf X iJ iQ n0 b₀ oldB strB carB) (t, a.2) (t', a'.2))
      (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).err ∧
    Err.Below (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).err ((2 : ℝ≥0∞)⁻¹ ^ r.set.target) :=
  k2_leads_seated (Cl₀ := Unit) h hW X iJ iQ d₁ d₂ ρ w p base ext strs inX on hon hpr hA n0 b₀ oldB
    strB carB hR hN B enter leave hX.rounds hX.step ext'

/-- **What the row says of one seated block b at the address a, with the law**: the lot's numbers n
at that address; the planner's record f of the group, of which they are made; a word «stands» and a
door; and the law of the code switch at b behind that door, at the typed record made of f, with
every premise that is left, by name (K02LawOf). -/
def LawAt (Z : ProofFile.Pub) (G : ProofFile.Ground) (a : VerifiableInference.Desc.Place) (nm : String)
    (b : Block S ProofFile.Cl) : Prop :=
  ∃ (P : Prep) (n : Nums) (f : FrameN) (st : K2.At) (enter : S → Except String S)
    (leave : S → S → Except String S),
    prepOf Z G = some P ∧ numsAt P a.link = some n ∧
    P.frames[a.link.getD P.z.request.link.length]? = some f ∧
    Sits b (K2.codeSwitchKind (IM.k2P Z a nm st n) : Block S Unit) enter leave ∧
    ∀ (lo l : List (OracleShape × ℕ)) (kept : List ℕ),
      K02LawOf (rowOf P.z lo l kept f) (IM.k2P Z a nm st n) b enter leave

theorem lawAt_of {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : VerifiableInference.Desc.Place} {nm : String}
    {b : Block S ProofFile.Cl} {P : Prep} {n : Nums} {st : K2.At} {enter : S → Except String S}
    {leave : S → S → Except String S} (hP : prepOf Z G = some P) (hn : numsAt P a.link = some n)
    (hX : Sits b (K2.codeSwitchKind (IM.k2P Z a nm st n) : Block S Unit) enter leave) : LawAt Z G a nm b := by
  obtain ⟨f, lay, hf, _, _, _, h⟩ := k2P_p2At (Z := Z) (nm := nm) (st := st) hn
  exact ⟨P, n, f, st, enter, leave, hP, hn, hf, hX, fun lo l kept =>
    k02LawOf_of (h lo l kept) hX.rounds hX.step⟩

theorem lawAt_of_sitsAt {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : VerifiableInference.Desc.Place}
    {nm : String} {b : Block S ProofFile.Cl} (h : SitsAt Z G a nm b) : LawAt Z G a nm b := by
  obtain ⟨P, n, hP, hn, h⟩ := h
  rcases h with ⟨_, hX⟩ | ⟨_, _, _, _, hX⟩ | ⟨_, _, hX⟩
  · exact lawAt_of hP hn hX
  · exact lawAt_of hP hn hX
  · exact lawAt_of hP hn hX

theorem lawAt_of_sitsFramed {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : VerifiableInference.Desc.Place}
    {nm : String} {b : Block S ProofFile.Cl} {fb : Block S Unit} (h : SitsFramed Z G a nm b fb) :
    LawAt Z G a nm b := by
  obtain ⟨P, n, hP, hn, h⟩ := h
  rcases h with ⟨_, hX⟩ | ⟨_, _, _, _, hX⟩ | ⟨_, _, hX⟩
  · exact lawAt_of hP hn hX
  · exact lawAt_of hP hn hX
  · exact lawAt_of hP hn hX

theorem lawAt_of_sitsJoined {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : VerifiableInference.Desc.Place}
    {nm : String} {b : Block S ProofFile.Cl} {fr : Johnson.Desc.First.Walk.Seat.LinkFrame}
    (h : SitsJoined Z G a nm b fr) : LawAt Z G a nm b := by
  obtain ⟨P, n, hP, hn, h⟩ := h
  rcases h with ⟨_, _, _, _, hX⟩ | ⟨_, _, hX⟩
  · exact lawAt_of hP hn hX
  · exact lawAt_of hP hn hX

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
  {F : VerifiableInference.Desc.FileDescription ProofFile.Inst}

/-- **K02_sits AND THE LAW, ONE SENTENCE.** -/
theorem k02_sits_law (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) :
    ∃ Z Bs base c A B, IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B ∧
      (∀ l, 1 ≤ l → l < 24 → ∃ (b : Block S ProofFile.Cl) (nm : String),
        c.blocksInOrder[14 * l + 0 + 2]? = some b ∧ (b.planOk = true →
                   LawAt Z Bs.G₀ { chain := 1, link := some l, piece := 1, kind := .K2 } nm b)) ∧
      (∃ (b : Block S ProofFile.Cl) (nm : String), c.blocksInOrder[14 * 24 + 1 + 2]? = some b ∧
        (b.planOk = true →
          LawAt Z Bs.G₀ { chain := 1, link := some 24, piece := 2, kind := .K2 } nm b)) ∧
      (∃ (b : Block S ProofFile.Cl) (nm : String), c.back[0]? = some b ∧ (b.planOk = true →
                LawAt Z Bs.G₀ IM.k2PlaceF nm b)) := by
  obtain ⟨Z, Bs, base, c, A, B, O, h1, h2, h3⟩ := k02_sits_step hS hR hF
  refine ⟨Z, Bs, base, c, A, B, O, fun l a1 a24 => ?_, ?_, ?_⟩
  · obtain ⟨b, nm, hf, h⟩ := h1 l a1 a24
    refine ⟨b, nm, hf, fun hp => ?_⟩
    obtain ⟨_, _, _, _, h⟩ := h hp
    exact lawAt_of_sitsJoined h
  · obtain ⟨b, nm, hf, h⟩ := h2
    exact ⟨b, nm, hf, fun hp => lawAt_of_sitsAt (h hp)⟩
  · obtain ⟨b, nm, hf, h⟩ := h3
    exact ⟨b, nm, hf, fun hp => lawAt_of_sitsAt (h hp)⟩

end

/-! ## The doors by name -/

/-- The seat and the law at one named door. -/
def DoorLaw (P : Prep) (f : FrameN) (p : K2.P2) (b : Block S ProofFile.Cl) (enter : S → Except String S)
    (leave : S → S → Except String S) : Prop :=
  Sits b (K2.codeSwitchKind p : Block S Unit) enter leave ∧
    ∀ (lo l : List (OracleShape × ℕ)) (kept : List ℕ),
      K02LawOf (rowOf P.z lo l kept f) p b enter leave

theorem doorLaw_of {Z : ProofFile.Pub} {a : VerifiableInference.Desc.Place} {nm : String}
    {b : Block S ProofFile.Cl} {P : Prep} {n : Nums} {f : FrameN} {st : K2.At}
    {enter : S → Except String S} {leave : S → S → Except String S}
    (h : ∀ (lo l : List (OracleShape × ℕ)) (kept : List ℕ),
      P2At (rowOf P.z lo l kept f) (IM.k2P Z a nm st n))
    (hX : Sits b (K2.codeSwitchKind (IM.k2P Z a nm st n) : Block S Unit) enter leave) :
    DoorLaw P f (IM.k2P Z a nm st n) b enter leave :=
  ⟨hX, fun lo l kept => k02LawOf_of (h lo l kept) hX.rounds hX.step⟩

/-- **LawAt with SitsAt's arms kept**: which «stands» and which door, dress by dress. -/
def LawArms (Z : ProofFile.Pub) (G : ProofFile.Ground) (a : VerifiableInference.Desc.Place) (nm : String)
    (b : Block S ProofFile.Cl) : Prop :=
  ∃ (P : Prep) (n : Nums) (f : FrameN), prepOf Z G = some P ∧ numsAt P a.link = some n ∧
    P.frames[a.link.getD P.z.request.link.length]? = some f ∧
    ((a.link = none ∧ DoorLaw P f (IM.k2P Z a nm .finish n) b K2.finishFrontQ
        (fun s t => (K2.finishBehindQ t).bind (guards s))) ∨
      (∃ l HP, a.link = some l ∧ pureLetters G l = some HP ∧
        DoorLaw P f (IM.k2P Z a nm .head n) b (fun s => .ok s)
          (fun s t => (K2.headOpenQ HP t).bind (guards s))) ∨
      (∃ l, a.link = some l ∧ DoorLaw P f (IM.k2P Z a nm .link n) b (fun s => .ok s)
        (fun s t => guards s t)))

/-- The like where a block fb of the frames' lot is joined behind. -/
def LawArmsFramed (Z : ProofFile.Pub) (G : ProofFile.Ground) (a : VerifiableInference.Desc.Place)
    (nm : String) (b : Block S ProofFile.Cl) (fb : Block S Unit) : Prop :=
  ∃ (P : Prep) (n : Nums) (f : FrameN), prepOf Z G = some P ∧ numsAt P a.link = some n ∧
    P.frames[a.link.getD P.z.request.link.length]? = some f ∧
    ((a.link = none ∧ DoorLaw P f (IM.k2P Z a nm .finish n) b K2.finishFrontQ
        (leaveWith (fun _ t => K2.finishBehindQ t) (ProofFile.guardMark fb.retype))) ∨
      (∃ l HP, a.link = some l ∧ pureLetters G l = some HP ∧
        DoorLaw P f (IM.k2P Z a nm .head n) b (fun s => .ok s)
          (leaveWith (fun _ t => K2.headOpenQ HP t) (ProofFile.guardMark fb.retype))) ∨
      (∃ l, a.link = some l ∧ DoorLaw P f (IM.k2P Z a nm .link n) b (fun s => .ok s)
        (leaveWith (fun _ t => .ok t) (ProofFile.guardMark fb.retype))))

theorem lawArms_of_sitsAt {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : VerifiableInference.Desc.Place}
    {nm : String} {b : Block S ProofFile.Cl} (h : SitsAt Z G a nm b) : LawArms Z G a nm b := by
  obtain ⟨P, n, hP, hn, h⟩ := h
  rcases h with ⟨ha, hX⟩ | ⟨l, HP, ha, hH, hX⟩ | ⟨l, ha, hX⟩
  · obtain ⟨f, _, hf, _, _, _, k⟩ := k2P_p2At (Z := Z) (nm := nm) (st := .finish) hn
    exact ⟨P, n, f, hP, hn, hf, Or.inl ⟨ha, doorLaw_of k hX⟩⟩
  · obtain ⟨f, _, hf, _, _, _, k⟩ := k2P_p2At (Z := Z) (nm := nm) (st := .head) hn
    exact ⟨P, n, f, hP, hn, hf, Or.inr (Or.inl ⟨l, HP, ha, hH, doorLaw_of k hX⟩)⟩
  · obtain ⟨f, _, hf, _, _, _, k⟩ := k2P_p2At (Z := Z) (nm := nm) (st := .link) hn
    exact ⟨P, n, f, hP, hn, hf, Or.inr (Or.inr ⟨l, ha, doorLaw_of k hX⟩)⟩

theorem lawArms_of_sitsFramed {Z : ProofFile.Pub} {G : ProofFile.Ground}
    {a : VerifiableInference.Desc.Place} {nm : String} {b : Block S ProofFile.Cl} {fb : Block S Unit}
    (h : SitsFramed Z G a nm b fb) : LawArmsFramed Z G a nm b fb := by
  obtain ⟨P, n, hP, hn, h⟩ := h
  rcases h with ⟨ha, hX⟩ | ⟨l, HP, ha, hH, hX⟩ | ⟨l, ha, hX⟩
  · obtain ⟨f, _, hf, _, _, _, k⟩ := k2P_p2At (Z := Z) (nm := nm) (st := .finish) hn
    exact ⟨P, n, f, hP, hn, hf, Or.inl ⟨ha, doorLaw_of k hX⟩⟩
  · obtain ⟨f, _, hf, _, _, _, k⟩ := k2P_p2At (Z := Z) (nm := nm) (st := .head) hn
    exact ⟨P, n, f, hP, hn, hf, Or.inr (Or.inl ⟨l, HP, ha, hH, doorLaw_of k hX⟩)⟩
  · obtain ⟨f, _, hf, _, _, _, k⟩ := k2P_p2At (Z := Z) (nm := nm) (st := .link) hn
    exact ⟨P, n, f, hP, hn, hf, Or.inr (Or.inr ⟨l, ha, doorLaw_of k hX⟩)⟩

/-- At a link's first place, with the link's own row fr of framesOf: SitsJoined's two arms kept. -/
def LawJoined (Z : ProofFile.Pub) (G : ProofFile.Ground) (a : VerifiableInference.Desc.Place) (nm : String)
    (b : Block S ProofFile.Cl) (fr : Johnson.Desc.First.Walk.Seat.LinkFrame) : Prop :=
  ∃ (P : Prep) (n : Nums) (f : FrameN), prepOf Z G = some P ∧ numsAt P a.link = some n ∧
    P.frames[a.link.getD P.z.request.link.length]? = some f ∧
    ((∃ l HP, a.link = some l ∧ pureLetters G l = some HP ∧
        DoorLaw P f (IM.k2P Z a nm .head n) b (fun s => .ok s)
          (fun s t => (K2.headOpenQ HP t).bind (leaveOpened fr s))) ∨
      (∃ l, a.link = some l ∧ DoorLaw P f (IM.k2P Z a nm .link n) b (fun s => .ok s)
        (fun s t => leaveOpened fr s t)))

theorem lawJoined_of_sitsJoined {Z : ProofFile.Pub} {G : ProofFile.Ground}
    {a : VerifiableInference.Desc.Place} {nm : String} {b : Block S ProofFile.Cl}
    {fr : Johnson.Desc.First.Walk.Seat.LinkFrame} (h : SitsJoined Z G a nm b fr) :
    LawJoined Z G a nm b fr := by
  obtain ⟨P, n, hP, hn, h⟩ := h
  rcases h with ⟨l, HP, ha, hH, hX⟩ | ⟨l, ha, hX⟩
  · obtain ⟨f, _, hf, _, _, _, k⟩ := k2P_p2At (Z := Z) (nm := nm) (st := .head) hn
    exact ⟨P, n, f, hP, hn, hf, Or.inl ⟨l, HP, ha, hH, doorLaw_of k hX⟩⟩
  · obtain ⟨f, _, hf, _, _, _, k⟩ := k2P_p2At (Z := Z) (nm := nm) (st := .link) hn
    exact ⟨P, n, f, hP, hn, hf, Or.inr ⟨l, ha, doorLaw_of k hX⟩⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
  {F : VerifiableInference.Desc.FileDescription ProofFile.Inst}

/-- **K02_sits AND THE LAW, ONE SENTENCE, THE DOORS BY NAME.** -/
theorem k02_sits_law_named (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) :
    ∃ Z Bs base c A B, IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B ∧
      (∀ l, 1 ≤ l → l < 24 → ∃ (b : Block S ProofFile.Cl) (nm : String),
        c.blocksInOrder[14 * l + 0 + 2]? = some b ∧ (b.planOk = true →
                   ∃ fs fr, Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
                     fs[l]? = some fr ∧
                     LawJoined Z Bs.G₀ { chain := 1, link := some l, piece := 1, kind := .K2 } nm b fr)) ∧
      (∃ (b : Block S ProofFile.Cl) (nm : String), c.blocksInOrder[14 * 24 + 1 + 2]? = some b ∧
        (b.planOk = true →
          LawArms Z Bs.G₀ { chain := 1, link := some 24, piece := 2, kind := .K2 } nm b)) ∧
      (∃ (b : Block S ProofFile.Cl) (nm : String), c.back[0]? = some b ∧ (b.planOk = true →
                LawArms Z Bs.G₀ IM.k2PlaceF nm b)) := by
  obtain ⟨Z, Bs, base, c, A, B, O, h1, h2, h3⟩ := k02_sits_step hS hR hF
  refine ⟨Z, Bs, base, c, A, B, O, fun l a1 a24 => ?_, ?_, ?_⟩
  · obtain ⟨b, nm, hf, h⟩ := h1 l a1 a24
    refine ⟨b, nm, hf, fun hp => ?_⟩
    obtain ⟨fs, fr, hfs, hfr, h⟩ := h hp
    exact ⟨fs, fr, hfs, hfr, lawJoined_of_sitsJoined h⟩
  · obtain ⟨b, nm, hf, h⟩ := h2
    exact ⟨b, nm, hf, fun hp => lawArms_of_sitsAt (h hp)⟩
  · obtain ⟨b, nm, hf, h⟩ := h3
    exact ⟨b, nm, hf, fun hp => lawArms_of_sitsAt (h hp)⟩

end

end P1K2

#print axioms P1K2.k02_sits_law_named
#print axioms P1K2.lawAt_of
#print axioms P1K2.k02_sits_law
#print axioms P1K2.k2P_p2At
#print axioms P1K2.k02_leads_of_sits
