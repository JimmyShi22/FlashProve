-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/BehindPaid.lean: `BehindAlike` (BehindAt.lean) IS PAID: a reading fb of the
piece's statement behind is written, and at every yes it is alike to the typed statement behind that
`lawOut` puts out.

Main names:
  `jointIs_at`: the joint seed that the reading of ReadingRd.lean makes of round 1's draws is
    `JointIs` (Johnson/Top/H0/K2Hands/SeedJoint.lean): just bMax + 1 elements, each coordinate the
    element read, THE FACTOR A UNIT's VALUE: the written sampler's draw that must not be 0 reads as
    an element other than 0 (`elemsV_nz`, OnBytes/Slice/Draws.lean). No premise but `K2Wr` and the
    round's test of work.
  `ansOf_getD`: the answers off a view whose first items are answers.
  `newSmp`, `newSmp_mat`: a new member's sample read off a record: a seed, BY CHOICE, whose matrix
    is the stored sample row's form (`K2.formsAt`), and the stored row's target (`K2.ansAt`).
  `fbOf`: THE READING: the new members' samples by `newSmp`; the old open messages' samples, all
    words and the carried joint's part by three letters; what the law does not read from a fixed
    statement.
  `Rides`: NAMED PREMISE 1: at every yes the three letters give back the old open messages' samples
    and the carried joint's part as they stood in front, and the words: the old open ones as they
    stood, the new ones as `WordsOf` reads them off the first written message.
  `FrontNums`: NAMED PREMISE 2: public numbers of the front that the text makes of a record with on:
    the codes are the typed record's; the number of messages in front is n0; `Tied`: member i of the
    typed list is the sending's notice number i, with one answer, in CaseE or CaseF.
  `behindAlike_paid`: from these two. By `seedIs_sig` (SeedJoint.lean) and `ans_behind`
    (Johnson/Top/H0/K2Hears/AnsBehind.lean).
  `k2_leads_read`: `k2_leads_alike` at `fbOf`.
Limits. `Rides` and `FrontNums` are shown at no real place. `Tied` can hold only if the typed list
covers every notice with an answer, these stand first, and each has one answer. A seed by choice:
nothing says that it is the seed that was drawn; its matrix is. Nothing on an old message's stored
sample. Those of BehindAt.lean. It is no soundness of the protocol. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.BehindAt
import Johnson.Top.H0.K2Caller.ReadOkAt
import Johnson.Top.H0.K2Hands.SeedJoint
import Johnson.Top.H0.K2Hears.AnsBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open OnBytes.Tie.Pv.Row (rvOne)
open VerifiableInference.Desc (Block Claim noDigest chainAt viewWordsBelowPrime)
open VerifiableInference.Desc.Sound (Frame Piece below)
open VerifiableInference.Desc.First.K2Hands
open _root_.Run (ckP)
open _root_.Tw.K2 (switchNotices)
open scoped ENNReal

/-- Two readings of a list of drawn elements. -/
theorem getD_toE : ∀ (L : List Fmt.Ext) (t : ℕ),
    (L.map toE).getD t 0 = readL (L.map E.ofTriple) t
  | [], _ => readE_zero.symm
  | x :: _, 0 => (readE_ofTriple x).symm
  | _ :: L, t + 1 => getD_toE L t

section
variable {r : SwRow} {H : r.OK} (X : Letters r H)
  (iJ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
  (d₁ d₂ : RDT) (ρ : WordsOf (selZ X iJ iQ) d₁)

/-- **The joint seed that the reading makes of round 1's draws is what round 1 drew, read**, the
factor a unit's value. -/
theorem jointIs_at (w : K2Wr r d₁ d₂) (m : (wT d₁).Msg) (c : (wT d₁).Chal)
    (hp : passOf d₁ c = true) (sd : (Fin (bMax r.cs r.l) → GE) × GEˣ)
    (h : (rdOf (X.withSel iJ iQ) d₁ d₂ ρ).rdSeed
      ((rdOf (X.withSel iJ iQ) d₁ d₂ ρ).view₁ m c).drawn = some sd) :
    JointIs r.cs r.l (vN d₁ m c) sd := by
  have hv : ((rdOf (X.withSel iJ iQ) d₁ d₂ ρ).view₁ m c).drawn.elems = (rvOne d₁ m c).drawn.elems :=
    (readOK_at X iJ iQ d₁ d₂ ρ w).elems m c hp
  have hlen : (rvOne d₁ m c).drawn.elems.length = bMax r.cs r.l + 1 := by
    have e := elems_len d₁ d₂ H w m c
    rwa [List.length_map] at e
  have h' : seedOfD (bMax r.cs r.l) ((rdOf (X.withSel iJ iQ) d₁ d₂ ρ).view₁ m c).drawn = some sd :=
      h
  unfold seedOfD at h'
  rw [hv, if_pos (by rw [List.length_map]; exact hlen)] at h'
  obtain rfl := Option.some.inj h'
  have hE : d₁.entry.drawE = bMax r.cs r.l + 1 := by
    rw [w.e₁]
    show r.set.samples * (largestCube r.o + 1) = _
    rw [H.samples, H.cube, Nat.one_mul]
  have hZ : d₁.entry.drawNZ = 1 := by
    rw [w.e₁]
    exact H.samples
  have hnz : ((rvOne d₁ m c).drawn.elems.map toE).getD (bMax r.cs r.l) 0 ≠ 0 := by
    rw [rvOne_elems]
    refine elemsV_nz _ _ ?_ _
    have hz := isNZ_dsOf_seed d₁.entry hZ
    rw [hE, Nat.add_sub_cancel] at hz
    show IsNZ (Fmt.dsOf d₁.entry d₁.kind) _
    rw [w.kind₁]
    exact hz
  exact ⟨hlen, fun t => getD_toE _ _, (unitOf_val hnz).trans (getD_toE _ _)⟩

end

/-- The answers off a view whose first N items are answers. -/
theorem ansOf_getD (d : Fmt.Drawn) : ∀ (vals : List Fmt.ItemValue) (N i : ℕ),
    (∀ k, k < N → ∃ t, vals[k]? = some (.answer t)) → i < N → ∀ t, vals[i]? = some (.answer t) →
    (OnBytes.Tie.Pv.Switch.ansOf ⟨vals, d⟩).getD i zeroE = E.ofTriple t
  | [], _, _, _, _, t, ht => by simp at ht
  | g :: vs, _, 0, _, _, t, ht => by
      have e : g = .answer t := by simpa using ht
      subst e
      rfl
  | g :: vs, N, i + 1, h, hi, t, ht => by
      obtain ⟨t0, h0⟩ := h 0 (by omega)
      have e0 : g = .answer t0 := by simpa using h0
      subst e0
      exact ansOf_getD d vs (N - 1) i
        (fun k hk => by
          have h1 := h (k + 1) (by omega)
          simpa using h1)
        (by omega) t (by simpa using ht)

variable {F : Frame} {W : Type}

section
variable {r : SwRow} {H : r.OK} (X : Letters r H)
  (iJ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
  (d₁ d₂ : RDT) (ρ : WordsOf (selZ X iJ iQ) d₁) (p : K2.P2) (base : ℕ)
  (ext : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → W → W)
  (strs : Rec × F.E.Str → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).Ex.Str)
  (inX : Rec → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).X)

open Classical in
/-- **A new member's sample, read off a record**: a seed whose matrix is the stored sample row's
form, if there is one; the stored row's target. n0: the number of the messages in front. -/
noncomputable def newSmp (n0 : ℕ) (s' : Rec) (o : Fin r.l.length) :
    ((sigOf r.cs r.l).om o).Smp :=
  (if h : ∃ z : ((sigOf r.cs r.l).om o).Z.D,
      (K2.formsAt r.cs (r.l.get o).1 s'.st (n0 + o.val) :
        Option (((sigOf r.cs r.l).om o).Z.S → ((sigOf r.cs r.l).om o).C.J → GE)) =
        some (((sigOf r.cs r.l).om o).Z.mat z) then h.choose else Classical.arbitrary _,
    (K2.ansAt s'.st (n0 + o.val)).getD fun _ => 0)

theorem newSmp_mat (n0 : ℕ) (s' : Rec) (o : Fin r.l.length) (z : ((sigOf r.cs r.l).om o).Z.D)
    (h : (K2.formsAt r.cs (r.l.get o).1 s'.st (n0 + o.val) :
        Option (((sigOf r.cs r.l).om o).Z.S → ((sigOf r.cs r.l).om o).C.J → GE)) =
        some (((sigOf r.cs r.l).om o).Z.mat z)) :
    ((sigOf r.cs r.l).om o).Z.mat (newSmp n0 s' o).1 = ((sigOf r.cs r.l).om o).Z.mat z := by
  have hex : ∃ z : ((sigOf r.cs r.l).om o).Z.D,
      (K2.formsAt r.cs (r.l.get o).1 s'.st (n0 + o.val) :
        Option (((sigOf r.cs r.l).om o).Z.S → ((sigOf r.cs r.l).om o).C.J → GE)) =
        some (((sigOf r.cs r.l).om o).Z.mat z) := ⟨z, h⟩
  have e : (newSmp n0 s' o).1 = hex.choose := dif_pos hex
  rw [e]
  exact Option.some.inj (hex.choose_spec.symm.trans h)

/-- **The reading fb**: the new members' samples off the record behind (`newSmp`); the old open
messages' samples, the words and the carried joint's part by three letters; the claim with the
positions, and the rider's word, which the law does not read, from a fixed statement b₀. -/
noncomputable def fbOf (n0 : ℕ) (b₀ : TB X iJ iQ)
    (oldB : Rec × F.E.Str → (selZ X iJ iQ).sw.S₀.Smp)
    (strB : Rec × F.E.Str → (selLoc X iJ iQ).S.ext.Str)
    (carB : Rec × F.E.Str → X.St₀ × X.E₀.Str) (a' : Rec × F.E.Str) : TB X iJ iQ :=
  (((b₀.1.1.1, (carB a').1),
      (selZ X iJ iQ).sw.S₀.join (selZ X iJ iQ).sw.d.N (T := OMsg.Smp) (oldB a')
        (newSmp n0 a'.1)),
    (((carB a').2, strB a'), b₀.2.2))

/-- **What rides**: at every yes the three letters give back what stood in front, and the words. -/
structure Rides (on : Rec × F.E.Str → Prop)
    (oldB : Rec × F.E.Str → (selZ X iJ iQ).sw.S₀.Smp)
    (strB : Rec × F.E.Str → (selLoc X iJ iQ).S.ext.Str)
    (carB : Rec × F.E.Str → X.St₀ × X.E₀.Str) : Prop where
  old : ∀ (a a' : Rec × F.E.Str) (τ : Tr (uLT (ckP .two) [d₁, d₂])), on a →
    (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).ior.red.out a τ = some a' →
    oldB a' = (lawFa X iJ iQ strs inX a).1.2
  str : ∀ (a a' : Rec × F.E.Str) (τ : Tr (uLT (ckP .two) [d₁, d₂])), on a →
    (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).ior.red.out a τ = some a' →
    strB a' = (selZ X iJ iQ).sw.S₀.join (selZ X iJ iQ).sw.d.N (T := OMsg.Str)
      (lawFa X iJ iQ strs inX a).2.2 (ρ.words τ.1)
  car : ∀ (a a' : Rec × F.E.Str) (τ : Tr (uLT (ckP .two) [d₁, d₂])), on a →
    (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).ior.red.out a τ = some a' →
    carB a' = ((lawFa X iJ iQ strs inX a).1.1.2, (lawFa X iJ iQ strs inX a).2.1.2)

/-- **What is asked of the front**: public numbers. -/
def FrontNums (n0 : ℕ) (on : Rec × F.E.Str → Prop) : Prop :=
  ∀ a, on a → ∀ fx, K2.frontAt p a.1 = some fx →
    fx.st.codes = r.cs ∧ fx.st.oracles.size = n0 ∧ Tied r.l (switchNotices fx.T fx.others)

set_option maxHeartbeats 2000000 in
/-- **`BehindAlike` is paid.** -/
theorem behindAlike_paid (w : K2Wr r d₁ d₂) (n0 : ℕ) (b₀ : TB X iJ iQ)
    (oldB : Rec × F.E.Str → (selZ X iJ iQ).sw.S₀.Smp)
    (strB : Rec × F.E.Str → (selLoc X iJ iQ).S.ext.Str)
    (carB : Rec × F.E.Str → X.St₀ × X.E₀.Str) (on : Rec × F.E.Str → Prop)
    (hR : Rides (W := W) X iJ iQ d₁ d₂ ρ p base ext strs inX on oldB strB carB)
    (hN : FrontNums (F := F) (r := r) p n0 on) :
    BehindAlike (W := W) X iJ iQ d₁ d₂ ρ p base ext strs inX on
      (fbOf X iJ iQ n0 b₀ oldB strB carB) := by
  intro a a' τ b₂ ha ho hl
  obtain ⟨q1, q2, ht, sd, Qs, hsd, hQs, e⟩ := outT_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      hl
  obtain ⟨fx, y, S3, Y, rows, G, c, A⟩ := K2.yes_whole p a.1 _ _ _ a'.1 ht
  obtain ⟨hc, hn, hT⟩ := hN a ha fx A.front
  have J := jointIs_at X iJ iQ d₁ d₂ ρ w τ.1 τ.2.1 q1 sd hsd
  have e' : b₂ = (rdOf (X.withSel iJ iQ) d₁ d₂ ρ).after (lawFa X iJ iQ strs inX a) sd Qs
      ((rdOf (X.withSel iJ iQ) d₁ d₂ ρ).answ τ.2.2.1) τ.1 := e
  have keyM : ∀ (cs : Codes), fx.st.codes = cs → ∀ (sd : (seedsOf cs r.l).D),
      JointIs cs r.l (vN d₁ τ.1 τ.2.1) sd → ∀ i : Fin r.l.length,
      (K2.formsAt cs (r.l.get i).1 a'.1.st (fx.st.oracles.size + i.val) :
        Option (((sigOf cs r.l).om i).Z.S → ((sigOf cs r.l).om i).C.J → GE)) =
        some (((sigOf cs r.l).om i).Z.mat ((seedsOf cs r.l).sd i sd)) := by
    rintro _ rfl sd J i
    exact seedIs_sig A r.l hT sd J i
  have hNs : ∀ i, i < r.l.length → ∃ n, (switchNotices fx.T fx.others)[i]? = some n ∧
      n.shape.answers = 1 := fun i hi => by
    obtain ⟨n, h1, -, h3, -⟩ := hT ⟨i, hi⟩
    exact ⟨n, h1, h3⟩
  subst e'
  refine ⟨fun i => ?_, fun i => ?_, ?_, ?_⟩
  · rcases i with i | o
    · show ((selLoc X iJ iQ).S.om (Sum.inl i)).Z.mat (oldB a' i).1 = _
      rw [hR.old a a' τ ha ho]
      rfl
    · have h1 := keyM r.cs hc sd J o
      rw [hn] at h1
      exact newSmp_mat n0 a'.1 o _ h1
  · rcases i with i | o
    · show (oldB a' i).2 = _
      rw [hR.old a a' τ ha ho]
      rfl
    · obtain ⟨t, h1, h2⟩ := K2.ans_behind A r.l.length hNs o.val o.isLt
      rw [hn] at h2
      show (K2.ansAt a'.1.st (n0 + o.val)).getD (fun _ => 0) = _
      rw [h2]
      funext s
      show readE (E.ofTriple t) = toE ((OnBytes.Tie.Pv.Switch.ansOf
        ((rdOf (X.withSel iJ iQ) d₁ d₂ ρ).view₂ τ.2.2.1 (Classical.choice (wT d₂).neChal))).getD
          o.val zeroE).triple
      have hv : ((rdOf (X.withSel iJ iQ) d₁ d₂ ρ).view₂ τ.2.2.1
          (Classical.choice (wT d₂).neChal)).vals = (vN d₂ τ.2.2.1 τ.2.2.2.1).vals := rfl
      have hg := ansOf_getD ((rdOf (X.withSel iJ iQ) d₁ d₂ ρ).view₂ τ.2.2.1
          (Classical.choice (wT d₂).neChal)).drawn (vN d₂ τ.2.2.1 τ.2.2.2.1).vals r.l.length o.val
        (fun k hk => by
          obtain ⟨t', h1', -⟩ := K2.ans_behind A r.l.length hNs k hk
          exact ⟨t', h1'⟩) o.isLt t h1
      rw [← hv] at hg
      rw [hg]
      rfl
  · exact hR.str a a' τ ha ho
  · exact hR.car a a' τ ha ho

end

set_option maxHeartbeats 2000000 in
/-- **The law of the piece's own reduction at the reading `fbOf`**: no premise on what stands behind
is left but `Rides` and `FrontNums`. -/
theorem k2_leads_read {r : SwRow} (h : r.ok = true) (hW : r.writtenOK = true)
    (X : Letters r (r.ok_says h))
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
    (hN : FrontNums (F := F) (r := r) p n0 on) :
    (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).ior.red.Leads on
      (fun a a' => ∀ wt,
        lawRb X iJ iQ p F.E.Str a (a'.1, fbOf X iJ iQ n0 b₀ oldB strB carB a') wt →
        ((Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).S.over
          (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).A).relR (lawFa X iJ iQ strs inX a)
            (selBk X iJ iQ wt) ∧
        ∀ k : (selHd X iJ iQ).K,
          ((selHd X iJ iQ).o k).decW ((selHd X iJ iQ).sW k (lawFa X iJ iQ strs inX a).2.1.1)
              ((lawFa X iJ iQ strs inX a).1.1.1.2 k) =
            some ((selHd X iJ iQ).msg (cutSel r.cs r.l iJ iQ (selNew X iJ iQ wt)).1 k))
      (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).err ∧
    Err.Below (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).err ((2 : ℝ≥0∞)⁻¹ ^ r.set.target) :=
  k2_leads_alike h hW X iJ iQ d₁ d₂ ρ w p base ext strs inX on hon hpr hA _
    (behindAlike_paid X iJ iQ d₁ d₂ ρ p base ext strs inX w n0 b₀ oldB strB carB on hR hN)

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.jointIs_at
#print axioms VerifiableInference.Desc.First.K2Caller.ansOf_getD
#print axioms VerifiableInference.Desc.First.K2Caller.newSmp_mat
#print axioms VerifiableInference.Desc.First.K2Caller.behindAlike_paid
#print axioms VerifiableInference.Desc.First.K2Caller.k2_leads_read
