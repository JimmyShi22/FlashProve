-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyGood21.lean: ROW 2.1 OF THE KEY FILE's TABLE OF JOINTS:
THE NAMED PREMISE KeyGood OF point_back₂ (Johnson/RunOne/KeyRow21.lean) CUT DOWN TO THE LIBRARY's
OWN NOTIONS: at BadKey := the library's bad points of the fold AT THE RECORD OF THE STATEMENT IN
FRONT (BadX2: Johnson/Desc/K14/Law/PointKey2.lean; Cb/Ld/LdFoldEq.lean: Bad), by PointKey2.lean's
good_of_notBad2; and the row with both named premises paid: point_back₂_lib.
ON EMPTINESS: as KeyRow21.lean's head: NO MEMBER OF on₂ … 1 IS SHOWN BY ANYBODY; NO MEMBER OF
DecTie | CollTie IS SHOWN.
OBJECT: KeyGood at ρ := Reading.gl, BadKey := BadX2 … · USER: point_back₂'s premise hgood · LETTERS:
the tables'; S is p.S; the library's letters err eM rank (PointKey2.lean's).
  nearAt_of_nearU    the tables' «NearU» gives K14's files' NearAt at the stored table's columns
    off the oracles: the converse of nearU_of_nearAt (no hA is needed this way)
  recAll_of_recRow   the tables' «RecRow» gives RecAll (after recAt_iff_recEq,
    Johnson/RunOne/KeyRow23.lean, which is not imported here: a near twin
    inside the proof)
  plainAt            a record of the shared chain at which a plain vector u IS «the folded row as
    the words hold it»: o_u's layout the identity
  DecTie             WHAT IS LEFT, UNDER on₂ … 1: where the library's decoder returns a table, the
    reading's decT returns cells, and KRead.tab reads them as that table on the places that hold the
    matrix. IT IS MORE THAN A TIE ON LETTERS: KRead.tab is F-valued, the library's decoder ranges
    over tables over the extension: DecTie can be met ONLY IF every table within eM columns of an
    F-valued word is F-valued: so where the generator matrix is over F and eM < the distance; false
    at eM ≥ the distance. OWED WITH IT, SHOWN BY NOBODY: eM < the distance · genOf over F · that
    lemma on the subfield
  keyGood_of_lib     PROVED FROM: hsame · henc · logN ≤ 32 · DecTie; of the promise it spends
    Free₂.fits; of the block's own test: index.ok and the matrix's room
  CollTie            A TIE ON LETTERS, UNDER on₂ … 1: the stored table has no collision at the
    key's seeds IN THE LIBRARY's SENSE (meant: out of FreeAt's letter coll)
  point_back₂_lib    **ROW 2.1, THE CHANCE's HALF, both named premises paid**: left: hbad · DecTie ·
    CollTie · PileTies (PAID at the tables' own letters: Johnson/RunOne/KeyPileTies.lean) · the
    letters' conditions · the written round
BARE «∀»: hbad [∀ f rec, over all tables over the extension,
under «no collision»]: the statement on codes' count AT THE TABLES' LETTER rad: AN INSTANCE THAT IS
NOT DEGENERATE: bad_le_efReal (Johnson/Goal/Numbers/K14BadAt.lean; by Lean, over foldErr_ix,
Johnson/Bridge/FoldErrIx.lean): at the release's code (a = 32 · r + l = 446693375 · v =
11), rad = 2852142980 ≤ eM < 3848273922: ef := efReal ≤ cMax |K| ^ 10: NOT YET CALLED HERE; it ties
rad ≤ eM < the distance, which DecTie wants too · hl · hsame · hpins · hof: as KeyRow21.lean's head
(hl | hpins are PAID: Johnson/RunOne/KeyRowsSeat.lean | KeyReadsH2.lean) · ha · hK · hd: public, no
statement in them.
good_of_notBad2 | ixOf2 | BadX2 | DecX2 | TabX2 (PointKey2.lean) and cnt_high | dotTrue_of |
linPoint_inv (PointGood.lean) lie in
Johnson/Desc/K14/Law/.
Nothing on soundness.
-/
import Johnson.RunOne.KeyPile21
import Johnson.Desc.K14.Law.PointKey2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open _root_.Iop (Reduction Err)
open _root_.Iop.IOR (drawRound)
open _root_.Prob (cnt)
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Plain
    VerifiableInference.Desc.Sound
open _root_.Desc.Plain (Par)
open _root_.Desc.K14.Law (LocAt NearAt tabOf codeVal locAt_iff RecAll RecAt RecEq eqK entry_eq
    weights_val UIsFold BadX2 DecX2 TabX2 good_of_notBad2 ixOf2 tabF seedsFn)
open _root_.Desc.K14.Law.ZetaWords (val_sumE)
open VerifiableInference.Desc.K13.Law (ρg)

section
variable {K : Type} [Field K] (ρ : Model.Reading K)

open Classical in
/-- **The tables' «NearU» gives K14's files' «near» (NearAt).** -/
theorem nearAt_of_nearU (Fr : Frame) (p : Par) (same : E → E → Prop) (hsame : ∀ x y, same x y ↔
    ρ.val x = ρ.val y)
    (enc : (Nat → E) → Nat → E) (henc : EncIs ρ p.S.fold enc) (d : St₂) (y : Fr.E.Str)
    (m : Means.Words K) (u : Nat → E) (hu : ∀ k, m d.loc.oU.oracle .main (d.loc.oU.lay.index k) =
        ρ.val (u k)) (e : Nat)
    (h : NearUAt same p.S.fold.index.code.logN e enc (d.loc.psiSh.drop p.S.kLo) (strsOf Fr y) u) :
    NearAt ρ p d m (tabOf y) e := by
  obtain ⟨B, hB, hall⟩ := h
  unfold NearAt
  refine le_trans (le_trans (Finset.card_le_card_of_injOn (t := B.toFinset) (fun x => x.val) ?_ (fun
      a _ b _ hab => Fin.ext hab)) (List.toFinset_card_le B)) hB
  intro x hx
  have hx' := (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
  refine Finset.mem_coe.2 (List.mem_toFinset.2 ?_)
  by_contra hn
  obtain ⟨c, hc, hs⟩ := hall x.val x.isLt hn
  refine hx' ((locAt_iff ρ p d m (tabOf y) x.val).2 ?_)
  have hc' : cellAt Fr y x.val = some c := hc
  unfold cellAt at hc'
  split at hc'
  · rename_i hxa
    obtain rfl := Option.some.inj hc'
    have e1 : tabOf y x.val = (y.1 ⟨x.val, hxa⟩).2 := by
      unfold tabOf
      rw [dif_pos hxa]
    rw [e1, ← (hsame _ _).1 hs, henc u x.val x.isLt]
    congr 1
    funext k
    exact hu k
  · cases hc'

/-- **The tables' «RecRow» gives (rec_gamma)'s equation at every seed.** -/
theorem recAll_of_recRow (p : Par) (same : E → E → Prop) (hsame : ∀ x y, same x y ↔ ρ.val x = ρ.val
    y) (d : St₂)
    (m : Means.Words K) (u : Nat → E) (hu : ∀ k, m d.loc.oU.oracle .main (d.loc.oU.lay.index k) =
        ρ.val (u k))
    (hfit : d.loc.key.fits p.S.fold.index = true) (hlen : (d.loc.psiSh.drop p.S.kLo).length =
        p.S.fold.index.v)
    (h : RecRowAt same p.S.fold.index d.loc.key (d.loc.psiSh.drop p.S.kLo) u) : RecAll ρ p d m := by
  intro x hx
  have hx' : d.loc.key.seeds[x.2]? = some x.1 := List.mem_zipIdx_iff_getElem?.1 hx
  simp only [TableKey.fits, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hfit
  have hlt : x.2 < p.S.fold.index.answers := by
    rw [← hfit.1.2]
    exact (List.getElem?_eq_some_iff.1 hx').1
  obtain ⟨seed, hs1, hs2⟩ := h x.2 hlt
  obtain rfl : x.1 = seed := Option.some.inj (hx'.symm.trans hs1)
  have h1 := (hsame _ _).1 hs2
  rw [ρ.add, val_sumE, val_sumE, val_sumE] at h1
  unfold RecAt RecEq
  have e1 : ∀ q ∈ Finset.range p.S.fold.index.plain, ρ.val (mulE ((Tensor.eq x.1.z).entry q) (u q))
      =
      eqK (x.1.z.map ρ.val) q * m d.loc.oU.oracle .main (d.loc.oU.lay.index q) := fun q _ => by
    rw [ρ.mul, entry_eq, ρ.one, one_mul, hu]
  have e2 : ∀ t ∈ Finset.range 3, ρ.val (mulE (mulE x.1.beta (thetaE t)) (u (p.S.fold.index.padPlace
      x.2 t))) =
      ρ.val x.1.beta * ρ.val (thetaE t) * m d.loc.oU.oracle .main (d.loc.oU.lay.index
          (p.S.fold.index.padPlace x.2 t)) := fun t _ => by
    rw [ρ.mul, ρ.mul, hu]
  have e3 : ∀ r ∈ Finset.range p.S.fold.index.rows,
      ρ.val (mulE ((Tensor.eq (d.loc.psiSh.drop p.S.kLo)).entry r) (d.loc.key.record.getD (r *
          p.S.fold.index.answers + x.2) zeroE)) =
      ρ.val ((_root_.Desc.K14.weights p.S d.loc).getD r zeroE) * ρ.val (d.loc.key.record.getD (r *
          p.S.fold.index.answers + x.2) zeroE) := fun r hr => by
    rw [ρ.mul, entry_eq, ρ.one, one_mul, weights_val ρ p.S d.loc r (by
      show r < 2 ^ (d.loc.psiSh.drop p.S.kLo).length
      rw [hlen]
      exact Finset.mem_range.1 hr)]
    rfl
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3] at h1
  exact h1

end

/-- A record of the shared chain at which a plain vector is «the folded row as the words hold it»:
the point's high part ga, the key, o_u's layout the identity. -/
def plainAt (kLo : Nat) (d : St₂) (key : TableKey) (ga : List E) : St₂ :=
  { d with loc := { d.loc with psiSh := List.replicate kLo zeroE ++ ga, oU := ⟨0, {}⟩, key := key }
      }

theorem plainAt_drop (kLo : Nat) (d : St₂) (key : TableKey) (ga : List E) : (plainAt kLo d key
    ga).loc.psiSh.drop kLo = ga :=
  List.drop_left' (by simp)

section
variable {XI Cells M Smp Rec Cl W : Type} {C : CK} (F : FileDescription XI) (Fr₂ : Frame)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (at_ : Where)
  (p : Par) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)
  (err eM : Nat) (rank : ((Fin p.S.fold.index.v → Bool) → Fin (p.S.fold.index.code.r +
      p.S.fold.index.code.ell) → Cb.Gl.E) → Nat)

/-- **A TIE ON LETTERS**: where the library's decoder returns a table, the reading's decT returns
cells, and KRead.tab reads them as that table on the places that hold the matrix. UNDER THE PROMISE
IN FRONT. -/
def DecTie : Prop :=
  ∀ (x : (P₂ × St₂) × Fr₂.E.Str), on₂ F Fr₂ G₂ at_ p.S K₁ R enc rad a coll last₁ off₂ 1 x →
    DecX2 p err eM rank (tabOf x.2) x.1.1.1.key →
    ∃ c, cellsAt G₂ x.1 (strsOf Fr₂ x.2) = some c ∧ ∀ r k, r < 2 ^ p.S.fold.index.v → k <
        p.S.matrixRows * 2 ^ p.S.kLo →
      ρg.val (ofF (R.tab c r k)) = TabX2 p err eM rank (tabOf x.2) x.1.1.1.key r k

/-- **KeyGood, cut down to the library's notions.** -/
theorem keyGood_of_lib (hsame : ∀ x y, R.same x y ↔ ρg.val x = ρg.val y) (henc : EncIs ρg p.S.fold
    enc)
    (ha : p.S.fold.index.code.logN ≤ 32)
    (hT : DecTie F Fr₂ G₂ at_ p K₁ R enc rad a coll last₁ off₂ err eM rank) :
    KeyGood F Fr₂ G₂ at_ p K₁ R enc rad a coll last₁ off₂ ρg
      (fun x gam => BadX2 p err eM rank rad (tabOf x.2) x.1.1.1.key gam) := by
  intro x gam ga u hx hlin hnb hga hN hR
  have hi := _root_.Desc.K14.Law.index_ok_of_linOk _ _ hlin
  have hroom := _root_.Desc.K14.Law.room_of_linOk _ _ hlin
  have hf : Free₂ F G₂ at_ p.S K₁ R coll last₁ off₂ 1 x.1 (strsOf Fr₂ x.2) := by
    rcases hx with hn | ⟨_, _, h3, _⟩
    · exact absurd trivial hn
    · exact h3
  have hd := plainAt_drop p.S.kLo x.1.2 x.1.1.1.key ga
  have hlen : ga.length = p.S.fold.index.v := by
    have := congrArg List.length hga
    simpa using this
  have hu : ∀ k, (fun (_ : Nat) (_ : Part) (i : Nat) => ρg.val (u i)) (plainAt p.S.kLo x.1.2
      x.1.1.1.key ga).loc.oU.oracle .main
      ((plainAt p.S.kLo x.1.2 x.1.1.1.key ga).loc.oU.lay.index k) = ρg.val (u k) := fun _ => rfl
  have h1 := nearAt_of_nearU ρg Fr₂ p R.same hsame enc henc (plainAt p.S.kLo x.1.2 x.1.1.1.key ga)
      x.2 (fun _ _ i => ρg.val (u i)) u hu rad (by rw [hd]; exact hN)
  have h2 := recAll_of_recRow ρg p R.same hsame (plainAt p.S.kLo x.1.2 x.1.1.1.key ga) (fun _ _ i =>
      ρg.val (u i)) u hu hf.fits (by rw [hd]; exact hlen) (by rw [hd]; exact hR)
  obtain ⟨hdec, hU⟩ := good_of_notBad2 p ha err eM rank rad (tabOf x.2) (plainAt p.S.kLo x.1.2
      x.1.1.1.key ga) (fun _ _ i => ρg.val (u i)) gam hi hroom hf.fits hnb
    (by
      show ((plainAt p.S.kLo x.1.2 x.1.1.1.key ga).loc.psiSh.drop p.S.kLo).map _ = _
      rw [hd]
      exact hga) h1 h2
  obtain ⟨c, hc, htab⟩ := hT x hx hdec
  refine ⟨c, hc, fun k hk => ?_⟩
  have e := hU k hk
  have e' : ρg.val (u k) = ∑ r ∈ Finset.range (2 ^ p.S.fold.index.v), eqK (List.ofFn gam) r * TabX2
      p err eM rank (tabOf x.2) x.1.1.1.key r k := e
  show ρg.val (u k) = _
  rw [e']
  refine Finset.sum_congr rfl fun r hr => ?_
  show _ = _ * ρg.val (ofF (R.tab c r k))
  rw [htab r k (Finset.mem_range.1 hr) hk]

/-- **A TIE ON LETTERS**: the stored table has no collision at the key's seeds, in the library's
sense. UNDER THE PROMISE IN FRONT. -/
def CollTie : Prop :=
  ∀ (x : (P₂ × St₂) × Fr₂.E.Str), on₂ F Fr₂ G₂ at_ p.S K₁ R enc rad a coll last₁ off₂ 1 x →
    ¬ (ixOf2 p.S.fold err eM rank).Coll (tabF ρg p.S.fold.index (tabOf x.2)) (seedsFn ρg
        p.S.fold.index x.1.1.1.key)

/-- **ROW 2.1, THE CHANCE's HALF, both named premises paid.** -/
theorem point_back₂_lib (pc : Piece C Fr₂ (P₂ × St₂) Cl W)
    (hl : ∀ z rs gs z', pc.b.decide z rs gs = .ok z' → z'.1 = z.1 ∧ _root_.Desc.K14.linPoint p z.2
        rs = some z'.2)
    (hbase : ∀ j ∈ pinned (open₂ 1), (at_ j).1 < pc.base)
    (hsame : ∀ x y, R.same x y ↔ ρg.val x = ρg.val y)
    (hpins : ∀ z z' : P₂ × St₂, z'.1 = z.1 → z'.2.st.oracles = z.2.st.oracles → z'.2.st.codes =
        z.2.st.codes → SamePins G₂ z z')
    (hof : ∀ (w : Wit Cells Unit M) c k, R.of { w with cells := c } k = R.of w k)
    (henc : EncIs ρg p.S.fold enc) (hK : K₁.lin = p.S)
    (ha : p.S.fold.index.code.logN ≤ 32)
    (ef c : Nat)
    (hc : ef * Fintype.card Cb.Gl.E ^ p.S.kLo + (p.S.kLo + p.S.fold.index.v) * Fintype.card Cb.Gl.E
        ^ (p.S.kLo + p.S.fold.index.v - 1) ≤ c)
    (hbad : ∀ f rec, ¬ (ixOf2 p.S.fold err eM rank).Coll f rec.1 → cnt ((ixOf2 p.S.fold err eM
        rank).Bad f rec rad) ≤ ef)
    (hcoll : CollTie F Fr₂ G₂ at_ p K₁ R enc rad a coll last₁ off₂ err eM rank)
    (hdec : DecTie F Fr₂ G₂ at_ p K₁ R enc rad a coll last₁ off₂ err eM rank)
    (hties : PileTies F Fr₂ G₂ at_ p K₁ R enc rad a coll last₁ off₂)
    (G : (P₂ × St₂) × Fr₂.E.Str → CarryS (uLT C pc.ds) [drawRound (Fin (p.S.kLo + p.S.fold.index.v)
        → Cb.Gl.E)])
    (fits : ∀ x, (G x).Fits ((c, ()) : Nat × Unit) pc.err)
    (hread : ∀ x τ x', on₂ F Fr₂ G₂ at_ p.S K₁ R enc rad a coll last₁ off₂ 1 x → pc.ior.red.out x τ
        = some x' →
      ∃ psi, (G x).tr τ = some (((), ()), psi, ()) ∧ x'.1.2.loc.psiSh.map ρg.val = List.ofFn psi) :
    pc.ior.red.Leads (on₂ F Fr₂ G₂ at_ p.S K₁ R enc rad a coll last₁ off₂ 1)
      (fun x x' => L₂ F Fr₂ G₂ at_ p.S K₁ R enc rad 2 x' → L₂ F Fr₂ G₂ at_ p.S K₁ R enc rad 1 x)
          pc.err :=
  point_back₂ F Fr₂ G₂ at_ p K₁ R enc rad a coll last₁ off₂ ρg pc hl hbase hsame hpins hof
    (fun x gam => BadX2 p err eM rank rad (tabOf x.2) x.1.1.1.key gam) ef c hc
    (fun x hx => hbad _ _ (hcoll x hx))
    (keyGood_of_lib F Fr₂ G₂ at_ p K₁ R enc rad a coll last₁ off₂ err eM rank hsame henc ha hdec)
    (pile_of_eval F Fr₂ G₂ at_ p K₁ R enc rad a coll last₁ off₂ hsame hK hties) G fits hread

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.nearAt_of_nearU
#print axioms Johnson.RunOne.KeyRows23.recAll_of_recRow
#print axioms Johnson.RunOne.KeyRows23.keyGood_of_lib
#print axioms Johnson.RunOne.KeyRows23.point_back₂_lib
