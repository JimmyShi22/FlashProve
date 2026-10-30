-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/KeysIx.lean: THE CLAIMS ON
KEYS THAT RIDE IN THE RECORD SEE, OF THE MASK ENTRIES, THE INDEX-MASK MESSAGE'S ALONE: at every
record that the key file's first chain reaches at a border from 2 to 15 (the lookups' links, and
the block behind them that lays the rows onto the ranges' group), the value of the mask form of
every claim on a lookup's keys is one at any two worlds of mask entries that agree on message number
0.

How: hear_course (Johnson/Desc/First/Look/KeyLaw/Out.lean) says, at
EVERY world, that the form which the hearing leaves for a part has the value of the course's own
claim on that part's leaves; the course's claim names the second ledger's entries alone (leaves_ix);
at the key file these are entries of message 0; the layer makes a claim's mask form of that form,
times -1.

Main names:
  KeysIx s: the sentence on a record.
  form_congr: a mask form's value reads the world at the slots that it names.
  forms_ix_of_hist: behind the kind's own block, off the history: the sentence on the forms heard.
  layer_ix: the claims on keys that the layer lays have the sentence.
  ix_of_hist: Hist₁ (Key.descriptionFromSource X N P) D k a ⊢ KeysIx a.2, 2 ≤ k ≤ 2 + 6 · the number of lookups.
  rows_of_ix: the sentence in the table's language: on the pending rows that keysAt reads.
  keys_ix_of_hist: at every border from 2 to 15, in the table's language.

Object: the first fifteen blocks of Key.descriptionFromSource X N P's first chain.
User: none yet (meant: the premise hmask of ride_15, KeyRide15.lean, at the field r1_15).
Letters: X, N, P, D · y: strings of the frame: rec_of_hist's letter; the statements do not read it.
Premises: those of rec_of_hist (RecOfHist.lean): planOk · RoomFor · the own message counts an
answer: the last two are theorems in scope (seat_in_scope, answers_in_scope) · for border 15: two
lookups (five_in_scope, held_full_two).
That the second ledger's entries are message 0's: off the record's half in front of the kind's block
(the table of homes is made of ⟨messageId, j⟩ and ⟨0, j⟩: homeT).

Limits. A sentence on values: a slot of another message may be named, where its coefficients'
readings cancel. Nothing on soundness.

-/
import Johnson.RunOne.Law.OutOfHist
import Johnson.RunOne.Law.OffWalk
import Johnson.RunOne.Law.CourseLeaves
import Johnson.RunOne.Law.TieTensor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.KeysIx
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat OnBytes.Slice
open OnBytes.Model (Fork)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (Xi FirstState Claim Source lookupSeat lookupLink lookupPlace)
open Johnson.RunOne.Sound (FK fk_K3_at fk_link_at)
open Johnson.RunOne.Law.AtKeyD
open Johnson.RunOne.Law.SeatsKeyD
open Johnson.RunOne.Law.JoinKeyD
open Johnson.RunOne.Law.LinkSeats
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.LinkAtFK
open Johnson.RunOne.Law.LinkAtCut
open Johnson.RunOne.Law.Walk
open Johnson.RunOne.Law.WalkAtFK
open Johnson.RunOne.Law.RecOfHist
open Johnson.RunOne.Law.K03KeySits
open Johnson.RunOne.Law.PromKeyD
open Johnson.RunOne.Law.FrontSteps
open Johnson.RunOne.Law.CourseLeaves
open LPFD (Hist₁ Reached)

/-- Every claim on keys in the record has a mask form whose value is one at any two worlds that
agree on message number 0. -/
def KeysIx (s : FirstState) : Prop :=
  ∀ keys ∈ s.base.keys, ∀ c ∈ keys, ∀ W W' : PscF.World,
    (∀ z : Slot, z.oracle = 0 → W.mask z = W'.mask z) →
    W.form (readForm c.masks) = W'.form (readForm c.masks)

/-- A mask form's value reads the world at the slots that it names. -/
theorem form_congr (W W' : PscF.World) (m : PscF.MaskForm)
    (h : ∀ q ∈ m, W.mask q.1 = W'.mask q.1) : W.form m = W'.form m := by
  unfold PscF.World.form
  exact congrArg List.sum (List.map_congr_left fun q hq => by rw [h q hq])

variable {X : Source} {N : H2U.PlaceNums} {P : VerifiableInference.Desc.Key.LaterPlaces}

/-- **Behind the kind's own block, off the history**: the form heard for a part, read at any later
ledger, has one value at any two worlds that agree on message number 0. -/
theorem forms_ix_of_hist (D : WholeD) (y : (frameAt D (allOf D) D.key₁ 0).E.Str)
    (hp : (FK X N P).planOk = true)
    (hR : RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
      X.Y.k.oneTime.indexMasks.shape)
    (ha : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0) (l : ℕ)
    (hl : l < X.Y.k.oneTime.ranges.lookups.length) (a : Xi × FirstState)
    (hH : Hist₁ (VerifiableInference.Desc.Key.descriptionFromSource X N P) D (2 + 6 * l + 3) a) (G : Fork)
    (g : HeardG) (hG : a.2.base.fork = some G) (hg : a.2.base.heard = some g)
    (H H' : Fork) (pl : List PlaneClaim) (u : OnBytes.K.Kc.Tape) (h1 : PscRun.Later G H)
    (h2 : planesG (faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
        X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime l))) g H [] = some (pl, H', u)) (K : Fork) (h3 :
            PscRun.Later H' K) (i : ℕ)
    (hi : i < (Lof X.Y.k.oneTime l).parts.length) (W W' : PscF.World)
    (hW : ∀ z : Slot, z.oracle = 0 → W.mask z = W'.mask z) :
    W.form (keyF K (fun j => a.2.base.home.getD j default) (g.keys.getD i (#[], {}))).masks =
      W'.form (keyF K (fun j => a.2.base.home.getD j default) (g.keys.getD i (#[], {}))).masks := by
  have hW0 := fk_admitted X N P hp
  have hadm := Lk6.adm_of_tests X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) _
    (tests_at hW0 hl).2.1 (tests_at hW0 hl).2.2
  obtain ⟨a', b, rs, cols, hr, hb, hd, -⟩ := Reached.last (k := 2 + 6 * l + 2) hH
  rw [List.getElem?_map] at hb
  obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
  have hk3 := fk_K3_at X N P l _ (look_at X.Y.k.oneTime l hl)
  rw [← Nat.add_assoc] at hk3
  obtain rfl := Option.some.inj (hk3.symm.trans hb₀)
  have hrec := rec_of_hist D y hp hR ha (2 + 6 * l + 2) (by omega) a' hr
  rw [Nat.add_assoc] at hrec
  obtain ⟨⟨hS, hI⟩, -⟩ := (recAt_link X l 2 (by omega) a'.2).1 hrec
  obtain ⟨-, hd'⟩ := VerifiableInference.Desc.Plain.held_decide _ _ _ _ _ hd
  obtain ⟨F, g0, G0, es, f1, f2, -, -, f5, f6⟩ := block_law _ _ _ _ _ hd'
  rw [f6] at hG hg ⊢
  obtain rfl : G0 = G := Option.some.inj hG
  obtain rfl : g0 = g := Option.some.inj hg
  obtain ⟨o, k, hk0, hh⟩ : ∃ o k : ℕ → Slot, (∀ n, (k n).oracle = 0) ∧ HomeIs (faceOfLkp
      (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime
          l))) 0 o k
      fun j => a'.2.base.home.getD j default := by
    rw [hI.1]
    refine ⟨_, _, fun n => ?_, homeIs_of_size _ _ _ hI.2.2.2.2⟩
    show (List.getD _ n default : Slot).oracle = 0
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases (handed (cntK X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
        X.Y.k.oneTime))
      (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) l)[n]? <;> rfl
  obtain ⟨hok, t, -, hm⟩ := hearE_inv f5
  have hf := faceIsK Unit X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
      X.Y.k.oneTime l) [] () hadm
    (d_le (tests_at hW0 hl).2.1)
  have hal : Al (fun j => a'.2.base.home.getD j default) o k (fromKeys (faceOfLkp (Wf.lookupOf
      X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime l)))) F.next
          0 0 := by
    rw [f2]
    exact al_of_homeIs hh
  have hi' : i < (datK Unit X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
      X.Y.k.oneTime l) []).m := by
    show i < ((Lof X.Y.k.oneTime l).parts.map _).length
    rw [List.length_map]
    exact hi
  obtain ⟨-, -, -, -, -, -, -, c8⟩ := hear_course W hf hadm hok hm (hS F f1) hal
  obtain ⟨-, -, -, -, -, -, -, c8'⟩ := hear_course W' hf hadm hok hm (hS F f1) hal
  have e1 := (((c8 H H' pl u h1 h2).2.2 K h3).1 i hi').2.2
  have e2 := (((c8' H H' pl u h1 h2).2.2 K h3).1 i hi').2.2
  show W.form (keyF K (fun j => a'.2.base.home.getD j default) (g0.keys.getD i (#[], {}))).masks =
    W'.form (keyF K (fun j => a'.2.base.home.getD j default) (g0.keys.getD i (#[], {}))).masks
  rw [e1, e2]
  refine form_congr W W' _ fun q hq => ?_
  obtain ⟨n, hn⟩ := leaves_ix _ _ 0 0 i hi' (hadm.bits i hi').1 q hq
  rw [hn]
  exact hW _ (hk0 n)

/-- **The step across the layer**: the claims on keys that it lays have the sentence. -/
theorem layer_ix (D : WholeD) (y : (frameAt D (allOf D) D.key₁ 0).E.Str)
    (hp : (FK X N P).planOk = true)
    (hR : RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
      X.Y.k.oneTime.indexMasks.shape)
    (ha : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0) (l : ℕ)
    (hl : l < X.Y.k.oneTime.ranges.lookups.length) (a : Xi × FirstState)
    (hH : Hist₁ (VerifiableInference.Desc.Key.descriptionFromSource X N P) D (2 + 6 * l + 3) a) (G : Fork)
    (g : HeardG) (hG : a.2.base.fork = some G) (hg : a.2.base.heard = some g)
    (k1 : g.keys.length = (Lof X.Y.k.oneTime l).parts.length)
    (pl : List PlaneClaim) (H' : Fork) (u : OnBytes.K.Kc.Tape)
    (p1 : planesG (faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
        X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime l))) g (G.paid g.owedObjects) [] = some (pl, H', u))
    (keys : List Lkp.Keys)
    (c5 : keyClaims (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
        X.Y.k.oneTime l))
      (H'.paid g.owedPlanes) a.2.base.home g = some keys) :
    ∀ c ∈ keys, ∀ W W' : PscF.World, (∀ z : Slot, z.oracle = 0 → W.mask z = W'.mask z) →
      W.form (readForm c.masks) = W'.form (readForm c.masks) := by
  intro c hc W W' hW
  unfold keyClaims at c5
  obtain ⟨kx, hkx, hk⟩ := Johnson.RunOne.Law.TieRows.mapM_mem _ _ _ c5 c hc
  obtain ⟨yy, hy, rfl⟩ := Option.map_eq_some_iff.1 hk
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hkx
  have hi' : i < g.keys.length := by rwa [List.length_zipIdx] at hi
  have hz : g.keys.zipIdx[i] = (g.keys.getD i (#[], {}), i) := by
    rw [List.getElem_zipIdx, Nat.zero_add, List.getD_eq_getElem]
  rw [hz] at hy
  have e := congrArg (·.masks) (keyF_reads (homeArr_getD a.2.base.home) hy)
  have e' : readForm yy.1 = (keyF (H'.paid g.owedPlanes) (fun n => a.2.base.home.getD n default)
      (g.keys.getD i (#[], {}))).masks := e
  show W.form (readForm (Psc.scaleForm (negE oneE) yy.1)) =
    W'.form (readForm (Psc.scaleForm (negE oneE) yy.1))
  rw [read_scaleForm, PscF.World.form_scale, PscF.World.form_scale, e',
    forms_ix_of_hist D y hp hR ha l hl a hH G g hG hg _ H' pl u (PscRun.paid_later _ _) p1 _
      (PscRun.paid_later _ _) i (k1 ▸ hi') W W' hW]

/-- **A RECORD THAT WAS REACHED HOLDS CLAIMS ON KEYS THAT SEE THE INDEX-MASK MESSAGE'S ENTRIES
ALONE**: up to the end of the lookups' links. -/
theorem ix_of_hist (D : WholeD) (y : (frameAt D (allOf D) D.key₁ 0).E.Str)
    (hp : (FK X N P).planOk = true)
    (hR : RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
      X.Y.k.oneTime.indexMasks.shape)
    (ha : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0) :
    ∀ (k : ℕ), 2 ≤ k → k ≤ 2 + 6 * X.Y.k.oneTime.ranges.lookups.length →
      ∀ a, Hist₁ (VerifiableInference.Desc.Key.descriptionFromSource X N P) D k a → KeysIx a.2
  | 0, h2, _, _, _ => absurd h2 (by omega)
  | k + 1, h2, hk, a, h => by
    rcases Nat.lt_or_ge k 2 with h6 | h6
    · obtain rfl : k = 1 := by omega
      have hr := (recAt_link X 0 0 (by omega) a.2).1 (rec_of_hist D y hp hR ha 2 hk a h)
      intro keys hkeys
      rw [List.length_eq_zero_iff.1 hr.2.1] at hkeys
      cases hkeys
    · obtain ⟨a', b, rs, cols, hr, hb, hd, hf⟩ := Reached.last h
      rw [List.getElem?_map] at hb
      obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
      obtain ⟨l, j, hj, rfl⟩ : ∃ l j, j < 6 ∧ k = 2 + (6 * l + j) :=
        ⟨(k - 2) / 6, (k - 2) % 6, Nat.mod_lt _ (by omega), by omega⟩
      have hl : l < X.Y.k.oneTime.ranges.lookups.length := by omega
      have hc := (fk_link_at X N P l j hj _ (look_at X.Y.k.oneTime l hl)).symm.trans hb₀
      have ih := ix_of_hist D y hp hR ha _ (by omega) (by omega) a' hr
      have hrec := (recAt_link X l j hj a'.2).1 (rec_of_hist D y hp hR ha _ (by omega) a' hr)
      have hy := (VerifiableInference.Desc.Plain.held_decide b₀ a' _ _ a hd).2
      obtain ⟨c0, c4, c5, hF, d0, d4, d5⟩ := link_flat X.Y.k.oneTime X.set l
        (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
            X.Y.k.oneTime l))
      rw [hF] at hc
      have c6 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
      rcases c6 with rfl | rfl | rfl | rfl | rfl | rfl
      · obtain rfl := Option.some.inj hc
        rw [d0] at hy
        rw [lay_same hy]
        exact ih
      · obtain rfl := Option.some.inj hc
        obtain ⟨-, -, o, kk, -, -, -, e⟩ := callerD_law hy
        rw [e]
        exact ih
      · obtain rfl := Option.some.inj hc
        obtain ⟨F, g, G, es, -, -, -, -, -, e⟩ := block_law _ _ _ _ _ hy
        rw [e]
        exact ih
      · obtain rfl := Option.some.inj hc
        obtain ⟨⟨hI, G, g, hG, hg, -, -, -, k1, -⟩, -⟩ := hrec
        obtain ⟨cls, s1, F, g', rows, keys, e1, e2, e3, -, e5, e⟩ := layerD_law hy
        obtain ⟨pl, H', u, p1, -, rfl⟩ := claimsD_law hG hg e1
        obtain rfl : H'.paid g.owedPlanes = F := Option.some.inj e2
        obtain rfl : g = g' := Option.some.inj ((show a'.2.base.heard = some g from hg).symm.trans
            e3)
        rw [e]
        intro ks hks
        rcases List.mem_append.1 hks with h1 | h1
        · exact ih ks h1
        · obtain rfl := List.mem_singleton.1 h1
          exact layer_ix D y hp hR ha l hl a' (by rw [Nat.add_assoc]; exact hr) G g hG hg
            (k1.trans (List.length_map _)) pl H' u p1 ks e5
      · obtain rfl := Option.some.inj hc
        rw [d4] at hy
        rw [after_same hy]
        exact ih
      · obtain rfl := Option.some.inj hc
        rw [d5] at hy
        rw [clear_eq hy]
        exact ih

/-- The sentence on a record, in the table's language: the READING of the mask form of every pending
row on a lookup's keys is one at any two mask worlds that read alike on message number 0. -/
theorem rows_of_ix (s : FirstState) (h : KeysIx s) (l : ℕ) (ks : List TensorRow)
    (hks : (Johnson.RunOne.KeyRows1.readers₁ X.Y.k.oneTime).keysAt s l = some ks) (x : TensorRow)
    (hx : x ∈ ks) (mk mk' : Slot → E) (hm : ∀ z : Slot, z.oracle = 0 → readE (mk z) = readE (mk' z))
        :
    readE (VerifiableInference.Desc.Key.formAt mk x.masks) =
      readE (VerifiableInference.Desc.Key.formAt mk' x.masks) := by
  have a2 : (s.base.keys[l]?).bind (Johnson.RunOne.KeyReaders.pendingOf X.Y.k.oneTime l) = some ks
      := hks
  obtain ⟨keys, b1, b2⟩ := Option.bind_eq_some_iff.1 a2
  unfold Johnson.RunOne.KeyReaders.pendingOf at b2
  obtain ⟨L', -, b3⟩ := Option.map_eq_some_iff.1 b2
  subst b3
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
  rw [Johnson.RunOne.Law.TieTensor.read_formAt, Johnson.RunOne.Law.TieTensor.read_formAt]
  exact h keys (List.mem_of_getElem? b1) q.2 (List.of_mem_zip hq).2 _ _ hm

/-- **AT EVERY BORDER FROM 2 TO 15.** -/
theorem keys_ix_of_hist (D : WholeD) (y : (frameAt D (allOf D) D.key₁ 0).E.Str)
    (hp : (FK X N P).planOk = true)
    (hR : RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
      X.Y.k.oneTime.indexMasks.shape)
    (ha : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0)
    (hn : X.Y.k.oneTime.ranges.lookups.length = 2) (k : ℕ) (h2 : 2 ≤ k) (h15 : k ≤ 15)
    (a : Xi × FirstState) (h : Hist₁ (VerifiableInference.Desc.Key.descriptionFromSource X N P) D k a) (l : ℕ)
    (ks : List TensorRow)
    (hks : (Johnson.RunOne.KeyRows1.readers₁ X.Y.k.oneTime).keysAt a.2 l = some ks) (x : TensorRow)
    (hx : x ∈ ks) (mk mk' : Slot → E) (hm : ∀ z : Slot, z.oracle = 0 → readE (mk z) = readE (mk' z))
        :
    readE (VerifiableInference.Desc.Key.formAt mk x.masks) =
      readE (VerifiableInference.Desc.Key.formAt mk' x.masks) := by
  refine rows_of_ix a.2 ?_ l ks hks x hx mk mk' hm
  rcases Nat.lt_or_ge k 15 with h14 | h14
  · exact ix_of_hist D y hp hR ha k h2 (by omega) a h
  · obtain rfl : k = 15 := by omega
    obtain ⟨a', b, rs, cols, hr, hb, hd, -⟩ := Reached.last (k := 14) h
    rw [List.getElem?_map] at hb
    obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
    have hrows := Johnson.RunOne.Sound.fk_rows_at X N P
    have hlen : (VerifiableInference.Desc.Key.lookupsOf X.Y.k.oneTime).length = 2 := by
      show (X.Y.k.oneTime.ranges.lookups.map _).length = 2
      rw [List.length_map, hn]
    rw [hlen] at hrows
    obtain rfl := Option.some.inj (hrows.symm.trans hb₀)
    have hy := (VerifiableInference.Desc.Plain.held_decide _ a' _ _ a hd).2
    have e := (rowsD_law hy).2.1
    intro keys hkeys
    rw [e] at hkeys
    exact ix_of_hist D y hp hR ha 14 (by omega) (by omega) a' hr keys hkeys

end Johnson.RunOne.Law.KeysIx

#print axioms Johnson.RunOne.Law.KeysIx.form_congr
#print axioms Johnson.RunOne.Law.KeysIx.forms_ix_of_hist
#print axioms Johnson.RunOne.Law.KeysIx.layer_ix
#print axioms Johnson.RunOne.Law.KeysIx.ix_of_hist
#print axioms Johnson.RunOne.Law.KeysIx.rows_of_ix
#print axioms Johnson.RunOne.Law.KeysIx.keys_ix_of_hist
