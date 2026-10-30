-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/KeySendRow.lean: THE TABLE OF JOINTS OF THE KEY FILE: THE ROW OF A SENDING, GENERAL: beside keeps_of_halves | emptyRow_keeps | rngRows_keeps (Johnson/Desc/Key/KeyKeeps.lean), in their form.
A SENDING CLOSES NOTHING AND OPENS pin k | srow k: so a true claim behind gives a true claim in front AT THE SAME WITNESS (back: the older items ride); ALL THE WEIGHT IS IN THE PROMISE BEHIND: of its four parts three hold FOR CERTAIN of whatever
the verifier puts out (sure: the book-keeping's Bool · the record holds the new sample · the promise's last letter; the older pins' samples are left) and ONE COSTS THE ERROR: NoColl at the new pin (law): the sending kind's files', IN THE PLAIN
ROAD's COIN: one Leads at the piece's own errors.
  noColl_ride      NoColl at an older pin rides: the same sample in the record, the same committed word
  sendRow_keeps    from sure · back · law ⟹ Keeps
  sendRow_keeps_fit   THE SAME WITH THE FORMAT's TEST ON THE ROUNDS AS A PREMISE OF sure | back: «roundsFit pc.b.rounds rs = true → pc.b.decide a (rs.map noDigest) gs = .ok b → …»: Block.step asks that test IN FRONT of decide: so a law of a kind that takes it
                   (decideSend_keeps) can be spent (piece_fits_at, Johnson/Desc/Plain/PieceFits.lean, beneath)
  leads_of_goodIn  Piece.GoodIn's coin into the plain road's: Piece.GoodIn on on' R R' gives Leads on (fun _ b => on' b) at the piece's own errors: BY DEFINITION AND Doomed.mono: the two coins are one game
  sendRow_keeps_sealed   THE FORM FOR THE CALLS: the rounds' test at hand; «law» from a kind's GoodIn; AND hasSmp AT THE NEW PIN TAKEN FROM THE LAW's PROMISE TOO (tie : Sl b → hasSmp ∧ NoColl: Johnson/Desc/Key/KeySealTie.lean's sealed_gives pays it from
                   «sealed» and SealReads): so (sure) speaks of the block's own text and of the elder pins alone, and asks nothing of the reading at the new pin
  sendRow_keeps_new   sendRow_keeps_sealed WITH A LETTER New : Strs → Prop: a fact of the PIECE on the strings behind (hnew), handed to (sure): for «every leaf of the new tenant's word is shown», which the promise behind is to gain: decide does not see how
                   the strings behind came
  sendRow_keeps_good   «law» had from a kind's GoodIn whose promise behind holds a fact Sl, and a tie «Sl b → NoColl at the new pin of b»
WHY NOT KeyQuiet.Rides: its field pins : SamePins asks the same sample at EVERY tenant: false across a sending (the new tenant's goes from none to some): here the ride is asked at the older pins alone.
EMPTY WHERE: the promise in front holds of nothing · the block refuses all · THE PIECE's ERRORS ARE AS LARGE AS A ROUND's NUMBER OF CHALLENGES: then «law» is true for nothing: the row is worth what «Err.Below pc.err …» is worth, which the frame asks
beside it by name. NOT HERE: that «law» holds at any piece · anything on srow k's truth (it is opened here, owed to the proximity test). Nothing on soundness by itself.
-/
import Johnson.Desc.Key.KeyKeeps
import Johnson.Desc.Sound.GoodIn
import Johnson.Desc.Plain.PieceFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK)
open _root_.Iop (Reduction)

section
variable {Xi P S Cells M Smp Rec Cl W : Type} {C : CK} (F : FileDescription Xi) (Fr : Frame) (G : Reading (P × S) Cells M Smp Rec) (at_ : Where)
  (Mg : KMeaning P S (Wit Cells Unit M))

/-- NoColl at a tenant rides where the record holds the same sample and the committed word is the same. -/
theorem noColl_ride (j t : Nat) (a b : P × S) (y y' : Strs) (hs : G.smp b j t = G.smp a j t) (hw : wordOf F y' j t = wordOf F y j t)
    (h : NoColl F G j t a y) : NoColl F G j t b y' := by
  intro o z ho hz m m' hm hm'
  exact h o z ho (hs ▸ hz) m m' ((member_congr F G o j t y y' z m hw).1 hm) ((member_congr F G o j t y y' z m' hw).1 hm')

/-- **The row of a sending.** -/
theorem sendRow_keeps (pc : Piece C Fr (P × S) Cl W) (shape shape' : S → Bool) (free free' : P × S → Strs → Prop) (O outs : List KItem) (k : Nat)
    (hk : pinned (O ++ outs) = pinned O ++ [k]) (hbase : ∀ j ∈ pinned O, (at_ j).1 < pc.base)
    (sure : ∀ a rs gs b y y', pc.b.decide a rs gs = .ok b → StrsStay F at_ O y y' → onAt F G at_ Mg shape free O a y →
      (Mg.unmarked b → Mg.unmarked a) ∧ (Mg.unmarked a → shape' b.2 = true ∧ hasSmp G (at_ k).1 (at_ k).2 b = true ∧
        (∀ j ∈ pinned O, G.smp b (at_ j).1 (at_ j).2 = G.smp a (at_ j).1 (at_ j).2) ∧ free' b y'))
    (back : ∀ a rs gs b y y' w, pc.b.decide a rs gs = .ok b → StrsStay F at_ O y y' → onAt F G at_ Mg shape free O a y →
      relAt F G at_ Mg (O ++ outs) b y' w → relAt F G at_ Mg O a y w)
    (law : pc.ior.red.Leads (onB F Fr G at_ Mg shape free O) (fun _ b => NoColl F G (at_ k).1 (at_ k).2 b.1 (strsOf Fr b.2)) pc.err) :
    pc.ior.red.Keeps (onB F Fr G at_ Mg shape free O) (onB F Fr G at_ Mg shape' free' (O ++ outs)) (claimB F Fr G at_ Mg O) (claimB F Fr G at_ Mg (O ++ outs)) pc.err := by
  unfold Reduction.Keeps
  refine Reduction.Leads.conseq law (fun _ h => h) fun a τ b ha hb hN => ?_
  have hd := piece_decides_at pc a τ b hb
  have Hy := strsStay_of_out F Fr at_ pc O hbase a b τ hb
  obtain ⟨hm, hs⟩ := sure a.1 _ _ b.1 _ _ hd Hy ha
  refine ⟨?_, fun ⟨w, hw⟩ => ⟨w, back a.1 _ _ b.1 _ _ w hd Hy ha hw⟩⟩
  by_cases hu : Mg.unmarked a.1
  · obtain ⟨h1, h2, h3, h4⟩ := hs hu
    have hr : shape a.1.2 = true ∧ ((pinned O).all fun k => hasSmp G (at_ k).1 (at_ k).2 a.1) = true ∧ free a.1 (strsOf Fr a.2) ∧
        ∀ k ∈ pinned O, NoColl F G (at_ k).1 (at_ k).2 a.1 (strsOf Fr a.2) := ha.resolve_left (fun hn => hn hu)
    refine Or.inr ⟨h1, ?_, h4, ?_⟩
    · rw [hk, List.all_append, Bool.and_eq_true]
      refine ⟨List.all_eq_true.2 fun j hj => ?_, by simpa using h2⟩
      have := List.all_eq_true.1 hr.2.1 j hj
      unfold hasSmp at this ⊢
      rw [h3 j hj]
      exact this
    · intro j hj
      rw [hk] at hj
      rcases List.mem_append.1 hj with hj | hj
      · exact noColl_ride F G _ _ a.1 b.1 _ _ (h3 j hj) (Hy.word j hj) (hr.2.2.2 j hj)
      · obtain rfl : j = k := by simpa using hj
        exact hN
  · exact Or.inl fun hb' => hu (hm hb')

/-- **The row of a sending, the rounds' test at hand.** -/
theorem sendRow_keeps_fit (pc : Piece C Fr (P × S) Cl W) (shape shape' : S → Bool) (free free' : P × S → Strs → Prop) (O outs : List KItem) (k : Nat)
    (hk : pinned (O ++ outs) = pinned O ++ [k]) (hbase : ∀ j ∈ pinned O, (at_ j).1 < pc.base)
    (sure : ∀ a rs gs b y y', roundsFit pc.b.rounds rs = true → pc.b.decide a (rs.map noDigest) gs = .ok b → StrsStay F at_ O y y' → onAt F G at_ Mg shape free O a y →
      (Mg.unmarked b → Mg.unmarked a) ∧ (Mg.unmarked a → shape' b.2 = true ∧ hasSmp G (at_ k).1 (at_ k).2 b = true ∧
        (∀ j ∈ pinned O, G.smp b (at_ j).1 (at_ j).2 = G.smp a (at_ j).1 (at_ j).2) ∧ free' b y'))
    (back : ∀ a rs gs b y y' w, roundsFit pc.b.rounds rs = true → pc.b.decide a (rs.map noDigest) gs = .ok b → StrsStay F at_ O y y' → onAt F G at_ Mg shape free O a y →
      relAt F G at_ Mg (O ++ outs) b y' w → relAt F G at_ Mg O a y w)
    (law : pc.ior.red.Leads (onB F Fr G at_ Mg shape free O) (fun _ b => NoColl F G (at_ k).1 (at_ k).2 b.1 (strsOf Fr b.2)) pc.err) :
    pc.ior.red.Keeps (onB F Fr G at_ Mg shape free O) (onB F Fr G at_ Mg shape' free' (O ++ outs)) (claimB F Fr G at_ Mg O) (claimB F Fr G at_ Mg (O ++ outs)) pc.err := by
  unfold Reduction.Keeps
  refine Reduction.Leads.conseq law (fun _ h => h) fun a τ b ha hb hN => ?_
  have hd := piece_decides_at pc a τ b hb
  have hf := (piece_fits_at pc a τ b hb).1
  have Hy := strsStay_of_out F Fr at_ pc O hbase a b τ hb
  obtain ⟨hm, hs⟩ := sure a.1 _ _ b.1 _ _ hf hd Hy ha
  refine ⟨?_, fun ⟨w, hw⟩ => ⟨w, back a.1 _ _ b.1 _ _ w hf hd Hy ha hw⟩⟩
  by_cases hu : Mg.unmarked a.1
  · obtain ⟨h1, h2, h3, h4⟩ := hs hu
    have hr : shape a.1.2 = true ∧ ((pinned O).all fun k => hasSmp G (at_ k).1 (at_ k).2 a.1) = true ∧ free a.1 (strsOf Fr a.2) ∧
        ∀ k ∈ pinned O, NoColl F G (at_ k).1 (at_ k).2 a.1 (strsOf Fr a.2) := ha.resolve_left (fun hn => hn hu)
    refine Or.inr ⟨h1, ?_, h4, ?_⟩
    · rw [hk, List.all_append, Bool.and_eq_true]
      refine ⟨List.all_eq_true.2 fun j hj => ?_, by simpa using h2⟩
      have := List.all_eq_true.1 hr.2.1 j hj
      unfold hasSmp at this ⊢
      rw [h3 j hj]
      exact this
    · intro j hj
      rw [hk] at hj
      rcases List.mem_append.1 hj with hj | hj
      · exact noColl_ride F G _ _ a.1 b.1 _ _ (h3 j hj) (Hy.word j hj) (hr.2.2.2 j hj)
      · obtain rfl : j = k := by simpa using hj
        exact hN
  · exact Or.inl fun hb' => hu (hm hb')

/-- **Piece.GoodIn's coin into the plain road's.** -/
theorem leads_of_goodIn (pc : Piece C Fr (P × S) Cl W) (on on' : (P × S) × Fr.E.Str → Prop) (Ra Rb : (P × S) × Fr.E.Str → W → Prop)
    (h : pc.GoodIn on on' Ra Rb) : pc.ior.red.Leads on (fun _ b => on' b) pc.err :=
  fun a ha => _root_.Iop.Doomed.mono _ _ (fun _ hτ b hb => (hτ b hb).1) (h a ha)

/-- **The row of a sending, its law had from the sending kind's GoodIn.** Sl: what that law's promise behind says of the new message (there: «sealed»); tie: that this gives NoColl at the table's pin: a fact on the reading G. -/
theorem sendRow_keeps_good (pc : Piece C Fr (P × S) Cl W) (shape shape' : S → Bool) (free free' : P × S → Strs → Prop) (O outs : List KItem) (k : Nat)
    (hk : pinned (O ++ outs) = pinned O ++ [k]) (hbase : ∀ j ∈ pinned O, (at_ j).1 < pc.base)
    (sure : ∀ a rs gs b y y', pc.b.decide a rs gs = .ok b → StrsStay F at_ O y y' → onAt F G at_ Mg shape free O a y →
      (Mg.unmarked b → Mg.unmarked a) ∧ (Mg.unmarked a → shape' b.2 = true ∧ hasSmp G (at_ k).1 (at_ k).2 b = true ∧
        (∀ j ∈ pinned O, G.smp b (at_ j).1 (at_ j).2 = G.smp a (at_ j).1 (at_ j).2) ∧ free' b y'))
    (back : ∀ a rs gs b y y' w, pc.b.decide a rs gs = .ok b → StrsStay F at_ O y y' → onAt F G at_ Mg shape free O a y →
      relAt F G at_ Mg (O ++ outs) b y' w → relAt F G at_ Mg O a y w)
    (Sl : (P × S) × Fr.E.Str → Prop) (Ra Rb : (P × S) × Fr.E.Str → W → Prop)
    (good : pc.GoodIn (onB F Fr G at_ Mg shape free O) Sl Ra Rb)
    (tie : ∀ b, Sl b → NoColl F G (at_ k).1 (at_ k).2 b.1 (strsOf Fr b.2)) :
    pc.ior.red.Keeps (onB F Fr G at_ Mg shape free O) (onB F Fr G at_ Mg shape' free' (O ++ outs)) (claimB F Fr G at_ Mg O) (claimB F Fr G at_ Mg (O ++ outs)) pc.err :=
  sendRow_keeps F Fr G at_ Mg pc shape shape' free free' O outs k hk hbase sure back
    (Reduction.Leads.conseq (leads_of_goodIn Fr pc _ _ _ _ good) (fun _ h => h) fun _ _ b _ _ hS => tie b hS)

/-- **The row of a sending, in the form for the calls.** -/
theorem sendRow_keeps_sealed (pc : Piece C Fr (P × S) Cl W) (shape shape' : S → Bool) (free free' : P × S → Strs → Prop) (O outs : List KItem) (k : Nat)
    (hk : pinned (O ++ outs) = pinned O ++ [k]) (hbase : ∀ j ∈ pinned O, (at_ j).1 < pc.base)
    (sure : ∀ a rs gs b y y', roundsFit pc.b.rounds rs = true → pc.b.decide a (rs.map noDigest) gs = .ok b → StrsStay F at_ O y y' → onAt F G at_ Mg shape free O a y →
      (Mg.unmarked b → Mg.unmarked a) ∧ (Mg.unmarked a → shape' b.2 = true ∧
        (∀ j ∈ pinned O, G.smp b (at_ j).1 (at_ j).2 = G.smp a (at_ j).1 (at_ j).2) ∧ free' b y'))
    (back : ∀ a rs gs b y y' w, roundsFit pc.b.rounds rs = true → pc.b.decide a (rs.map noDigest) gs = .ok b → StrsStay F at_ O y y' → onAt F G at_ Mg shape free O a y →
      relAt F G at_ Mg (O ++ outs) b y' w → relAt F G at_ Mg O a y w)
    (Sl : (P × S) × Fr.E.Str → Prop) (Ra Rb : (P × S) × Fr.E.Str → W → Prop)
    (good : pc.GoodIn (onB F Fr G at_ Mg shape free O) Sl Ra Rb)
    (tie : ∀ b, Sl b → hasSmp G (at_ k).1 (at_ k).2 b.1 = true ∧ NoColl F G (at_ k).1 (at_ k).2 b.1 (strsOf Fr b.2)) :
    pc.ior.red.Keeps (onB F Fr G at_ Mg shape free O) (onB F Fr G at_ Mg shape' free' (O ++ outs)) (claimB F Fr G at_ Mg O) (claimB F Fr G at_ Mg (O ++ outs)) pc.err := by
  unfold Reduction.Keeps
  refine Reduction.Leads.conseq (leads_of_goodIn Fr pc _ _ _ _ good) (fun _ h => h) fun a τ b ha hb hS => ?_
  obtain ⟨h2, hN⟩ := tie b hS
  have hd := piece_decides_at pc a τ b hb
  have hf := (piece_fits_at pc a τ b hb).1
  have Hy := strsStay_of_out F Fr at_ pc O hbase a b τ hb
  obtain ⟨hm, hs⟩ := sure a.1 _ _ b.1 _ _ hf hd Hy ha
  refine ⟨?_, fun ⟨w, hw⟩ => ⟨w, back a.1 _ _ b.1 _ _ w hf hd Hy ha hw⟩⟩
  by_cases hu : Mg.unmarked a.1
  · obtain ⟨h1, h3, h4⟩ := hs hu
    have hr : shape a.1.2 = true ∧ ((pinned O).all fun k => hasSmp G (at_ k).1 (at_ k).2 a.1) = true ∧ free a.1 (strsOf Fr a.2) ∧
        ∀ k ∈ pinned O, NoColl F G (at_ k).1 (at_ k).2 a.1 (strsOf Fr a.2) := ha.resolve_left (fun hn => hn hu)
    refine Or.inr ⟨h1, ?_, h4, ?_⟩
    · rw [hk, List.all_append, Bool.and_eq_true]
      refine ⟨List.all_eq_true.2 fun j hj => ?_, by simpa using h2⟩
      have := List.all_eq_true.1 hr.2.1 j hj
      unfold hasSmp at this ⊢
      rw [h3 j hj]
      exact this
    · intro j hj
      rw [hk] at hj
      rcases List.mem_append.1 hj with hj | hj
      · exact noColl_ride F G _ _ a.1 b.1 _ _ (h3 j hj) (Hy.word j hj) (hr.2.2.2 j hj)
      · obtain rfl : j = k := by simpa using hj
        exact hN
  · exact Or.inl fun hb' => hu (hm hb')

/-- **The same, with a fact of the PIECE on the strings behind at hand** (New: there: «every leaf of the new tenant's word is shown»): decide does not see how the strings behind came; the piece does. -/
theorem sendRow_keeps_new (pc : Piece C Fr (P × S) Cl W) (shape shape' : S → Bool) (free free' : P × S → Strs → Prop) (O outs : List KItem) (k : Nat)
    (hk : pinned (O ++ outs) = pinned O ++ [k]) (hbase : ∀ j ∈ pinned O, (at_ j).1 < pc.base)
    (New : Strs → Prop) (hnew : ∀ a τ b, onB F Fr G at_ Mg shape free O a → pc.ior.red.out a τ = some b → New (strsOf Fr b.2))
    (sure : ∀ a rs gs b y y', roundsFit pc.b.rounds rs = true → pc.b.decide a (rs.map noDigest) gs = .ok b → StrsStay F at_ O y y' → New y' → onAt F G at_ Mg shape free O a y →
      (Mg.unmarked b → Mg.unmarked a) ∧ (Mg.unmarked a → shape' b.2 = true ∧
        (∀ j ∈ pinned O, G.smp b (at_ j).1 (at_ j).2 = G.smp a (at_ j).1 (at_ j).2) ∧ free' b y'))
    (back : ∀ a rs gs b y y' w, roundsFit pc.b.rounds rs = true → pc.b.decide a (rs.map noDigest) gs = .ok b → StrsStay F at_ O y y' → onAt F G at_ Mg shape free O a y →
      relAt F G at_ Mg (O ++ outs) b y' w → relAt F G at_ Mg O a y w)
    (Sl : (P × S) × Fr.E.Str → Prop) (Ra Rb : (P × S) × Fr.E.Str → W → Prop)
    (good : pc.GoodIn (onB F Fr G at_ Mg shape free O) Sl Ra Rb)
    (tie : ∀ b, Sl b → hasSmp G (at_ k).1 (at_ k).2 b.1 = true ∧ NoColl F G (at_ k).1 (at_ k).2 b.1 (strsOf Fr b.2)) :
    pc.ior.red.Keeps (onB F Fr G at_ Mg shape free O) (onB F Fr G at_ Mg shape' free' (O ++ outs)) (claimB F Fr G at_ Mg O) (claimB F Fr G at_ Mg (O ++ outs)) pc.err := by
  unfold Reduction.Keeps
  refine Reduction.Leads.conseq (leads_of_goodIn Fr pc _ _ _ _ good) (fun _ h => h) fun a τ b ha hb hS => ?_
  obtain ⟨h2, hN⟩ := tie b hS
  have hd := piece_decides_at pc a τ b hb
  have hf := (piece_fits_at pc a τ b hb).1
  have Hy := strsStay_of_out F Fr at_ pc O hbase a b τ hb
  obtain ⟨hm, hs⟩ := sure a.1 _ _ b.1 _ _ hf hd Hy (hnew a τ b ha hb) ha
  refine ⟨?_, fun ⟨w, hw⟩ => ⟨w, back a.1 _ _ b.1 _ _ w hf hd Hy ha hw⟩⟩
  by_cases hu : Mg.unmarked a.1
  · obtain ⟨h1, h3, h4⟩ := hs hu
    have hr : shape a.1.2 = true ∧ ((pinned O).all fun k => hasSmp G (at_ k).1 (at_ k).2 a.1) = true ∧ free a.1 (strsOf Fr a.2) ∧
        ∀ k ∈ pinned O, NoColl F G (at_ k).1 (at_ k).2 a.1 (strsOf Fr a.2) := ha.resolve_left (fun hn => hn hu)
    refine Or.inr ⟨h1, ?_, h4, ?_⟩
    · rw [hk, List.all_append, Bool.and_eq_true]
      refine ⟨List.all_eq_true.2 fun j hj => ?_, by simpa using h2⟩
      have := List.all_eq_true.1 hr.2.1 j hj
      unfold hasSmp at this ⊢
      rw [h3 j hj]
      exact this
    · intro j hj
      rw [hk] at hj
      rcases List.mem_append.1 hj with hj | hj
      · exact noColl_ride F G _ _ a.1 b.1 _ _ (h3 j hj) (Hy.word j hj) (hr.2.2.2 j hj)
      · obtain rfl : j = k := by simpa using hj
        exact hN
  · exact Or.inl fun hb' => hu (hm hb')

end

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.sendRow_keeps_new
#print axioms VerifiableInference.Desc.Key.sendRow_keeps_sealed
#print axioms VerifiableInference.Desc.Key.sendRow_keeps_fit
#print axioms VerifiableInference.Desc.Key.leads_of_goodIn
#print axioms VerifiableInference.Desc.Key.sendRow_keeps_good
#print axioms VerifiableInference.Desc.Key.noColl_ride
#print axioms VerifiableInference.Desc.Key.sendRow_keeps
