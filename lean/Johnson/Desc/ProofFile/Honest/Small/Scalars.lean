-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/Scalars.lean proves `ExactMember` (Honest/Small/Field.lean: the
field `exact` of `Good`, Honest/Side.lean, without its hypothesis on the opened columns; it gives
that field at every `pre`) at one member, `scalarsPart name n vals` (one round that sends n scalars,
each as its value plus a mask entry) beside `scalarsSim a n` (Honest/ForKinds.lean), conditional on
the one premise hrs: the member's rounds rs are one round, which states n elements of the extension
field, no other item but roots, and no oracle message. It is the spender's half alone, one part at a
time, all else fixed before the coins. It is not a statement on whether the run that the part spends
is fresh in a run of the protocol, nor on whether the values are the protocol's, nor on a whole row,
nor on a part into which a stop has been laid, nor on one that is joined to another by
`Part.andThen`, nor on one that stands beside another simulator or another n. It is for every caller
whose round meets the premise.

  `scalarsPart_exact_lift`: at the part written at any types and seated by `Part.lift`, at every
     see, wit, get and set (the four together: the lens)
  `scalarsPart_exact`: at the bare part (not lifted), at all types at which there is a face
  the rest: the lemmas on the way: the sum of a list and a vector of coins; what is said, as a
     vector; that it has the stated shape; what the part shows and its simulator yields, as
     equations in the coins

The face, the side, chain, firstTree, On, bud, the member's number j, its rounds rs, the simulator's
address a, the run's name, n and vals are variables; the member is written out. Nothing is asked of
vals, of its list's length, of the input or of where the run stands.

What is sampled: on the part's side `Cs ⟨0, 0⟩ × (Cs ⟨0, n⟩ × Unit)`: the one run that the part
spends, taken as uniform by `ExactMember`'s own text, which is the field's there: n elements c of
the extension field; on the simulator's `Cs ⟨0, n⟩`: n uniform elements. Fixed: ca, m (so all that
vals reads: by type it is handed no coin), front, ds, asks. The part shows one round, the words of t
i + c i for i < n, where t is the values' list, padded or cut to n, read into the field (`valsAt`);
the simulator yields the words of c i. n coins against n scalars, one each: c to t + c is a
bijection of the vectors, at every t. Of the six premises of `ExactMember` `drawsFit` alone is used,
and of it only that ds is one challenge.

What is proved again here, and why. `padTo_len`, and the shape's lemma `fits_scalars`, have their
like in Honest/SumLaw/ (Lists.lean, Fits.lean: `padTo_length`, `sayE_fits`): they are proved again
here, under other names and by another proof, so that this file leans on the frame, the library and
Honest/Small/Field.lean alone. `bindNone` is the statement of `bind_to_none` in
Honest/Small/Quiet.lean: neither file imports the other. From the library: `addE_triple`
(OnBytes/Field/ExtEq.lean), `toE_addE`, `toE_ofE` (OnBytes/Slice/Field.lean).

The frame's terms that are used here (part, side, row, member, face, coin, run, book, fold and the
like): the head of Honest/Small/Field.lean. All names stand in the namespace ProofFile.Honest.Small: a
caller opens it.

Limits. Without hrs the equation fails: at a round that states another number of scalars the part is
at fault and shows the one symbol, and its simulator does not (said here without a theorem). That a
description's round states this shape is the caller's to show: this file shows it of none.
It reaches `ExactMember`, and through it `exact`, alone. It holds at every vals, right or wrong. A
padded or cut value is a wrong message in silence: wherever a sentence leans on which values are
sent (`acc`: that the verifier's step says yes; `plays`: the sentence B behind it), that the list
has n members, and which, is still owed.
The run. `ExactMember`, as the field `exact`, draws the spent run uniformly, apart from m: that is
taken, by the order of its own quantifiers; it is no premise and no type. That the book lends the
part just that run, that no part in front has been handed a coin of it, and the owner's `fresh` for
this spender, are not shown here: they are left to the owner's part, to the book's tests
(`ProverCoinCounts.clauses`) and to a rule that joins a row's parts, which no file that this one imports states.
The run's name is not read.
vals may read what was seen, heard and handed on: should any of that, or the input, hang on a coin
of this run in a real run, the equation says nothing on that run (said here without a theorem). The
run's owner always stands in front of its spender (the book's test): so the items in the clear that
the owner has shown are always among what vals can read (and, where columns are handed, so are the
opened columns that `Seen.opened` holds: by type, columns of the owner's tables can be among them):
for that stretch the owner's `fresh` alone pays: it speaks of what the owner shows, which is its
items in the clear and the columns of its own tables at the positions asks, and it is asked only at
positions within the owner's `bud`: that the columns handed lie at such positions is not shown here.
A vals that reads the columns cannot refuse where none are handed (`none`): it yields a list, and
the move always answers. The frame asks every part that reads them to return an error there
(`Seen.opened`, Honest/Frame.lean): a part of this form cannot. The equation holds of such a vals
all the same.
And whoever carries the run behind this part: the frame lets any part behind the spender carry it,
and c to t + c is one to one: what this part shows, together with the run, gives t at every coin: so
such a carrier has to meet its own `exact` at each fixed carried run, beside a simulator that is not
handed it; and a carrier's On may tie what is carried to the front only by an identity that holds at
every value of the carried run's coins: an On that picks among coins is what is barred; no type
refuses such an On: it leaves `exact` silent at the values of these coins at which it does not hold.
Both are for whoever writes the carrier to show.
hrs is wider than "just n scalars are sent". It lets through a round whose entry counts roots, or
has left-over bytes, with no oracle message. The part lays no table there, and what a part shows
never holds a root. `Block.shaped`, which the plan's test asks, refuses the first
(`roots_of_shaped`, Honest/Small/Field.lean), the format's `Round.ok` (Fmt/Rules8.lean) the second;
`Good` refuses neither.
hrs reads neither `DeclaredRound.stored` nor `DeclaredRound.opens` nor the work bits. The round may draw
positions at which trees and stored tables are opened: these columns are accounted for at the
sender's part and in `Before.stored`, not here.
What the part hands on is not in the equation. "At every set" is no word on the lens: behind its
round the seated part lays set x (get x) on what is handed on; what a later part then shows is that
part's own `exact`. wit and get are read: vals is handed the input through wit and what was handed
on through get. No lens reaches the coins, by type. And no lens narrows what was seen: `Move.lift`
passes it whole: a part written at small types is still handed every round shown in front and, where
columns are handed, the opened columns.
Nothing is claimed on any property of the protocol: not soundness, completeness, binding, hiding or
any other.
-/
import OnBytes.Field.ExtEq
import OnBytes.Slice.Field
import Johnson.Desc.ProofFile.Honest.ForKinds
import Johnson.Desc.ProofFile.Honest.Law.ToyLaw
import Johnson.Desc.ProofFile.Honest.Law.ToyPlay
import Johnson.Desc.ProofFile.Honest.Small.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Small
open VerifiableInference.Desc (Place Oracle itemOf)
open OnBytes.Slice (toE ofE)

variable {S Cl V W X Pb V' W' Y : Type}

/-! ## 1 Lists and vectors -/

/-- Binding any option to the function that always yields `none` gives `none`. `bind_to_none` in
Honest/Small/Quiet.lean is the same statement: neither file imports the other. -/
theorem bindNone {α β : Type} (o : Option α) :
    (o.bind fun _ => (none : Option β)) = none := by
  cases o <;> rfl

/-- The sum of a list of n elements and a vector of n. -/
theorem addL_ofFn (n : Nat) : ∀ (l : List OnBytes.E) (f : Fin n → OnBytes.E), l.length = n →
    addL l (List.ofFn f) = List.ofFn fun i => OnBytes.addE (l.getD i.1 OnBytes.zeroE) (f i) := by
  induction n with
  | zero =>
    intro l f h
    obtain rfl := List.length_eq_zero_iff.1 h
    rw [List.ofFn_zero, List.ofFn_zero]
    rfl
  | succ n ih =>
    intro l f h
    cases l with
    | nil => simp at h
    | cons x l =>
      rw [List.ofFn_succ, List.ofFn_succ]
      show OnBytes.addE x (f 0) :: addL l (List.ofFn fun i => f i.succ) = _
      rw [ih l (fun i => f i.succ) (by
        simp only [List.length_cons] at h
        omega)]
      simp only [Fin.val_zero, Fin.val_succ, List.getD_cons_zero, List.getD_cons_succ]

/-- A list padded or cut to n has n members. -/
theorem padTo_len (n : Nat) (a : List OnBytes.E) : (padTo n a).length = n := by
  simp [padTo]
  omega

/-- n coins of the extension field as a vector. -/
def eqE (n : Nat) : Cs ⟨0, n⟩ ≃ (Fin n → Cb.Gl.E) where
  toFun c := c.e
  invFun y := ⟨fun i => i.elim0, y⟩
  left_inv _ := Cs.ext' (fun i => i.elim0) (fun _ => rfl)
  right_inv _ := rfl

/-- No coin, beside one run of n coins of the extension field: as a vector. -/
def eq0E (name : String) (n : Nat) :
    Cs ⟨0, 0⟩ × CsAll [(name, (⟨0, n⟩ : Due))] ≃ (Fin n → Cb.Gl.E) where
  toFun c := c.2.1.e
  invFun y := (Cs.empty, ((eqE n).symm y, ()))
  left_inv c := Prod.ext (Cs.eq0.left_inv c.1) (Prod.ext ((eqE n).left_inv c.2.1) rfl)
  right_inv _ := rfl

/-- One round that shows n elements of the extension field, and no column. -/
def scalarsAt {n : Nat} (y : Fin n → Cb.Gl.E) : Option (List Shown) :=
  some [⟨List.ofFn fun i => .e (ofE (y i)), []⟩]

/-- A list of values, padded or cut to n, read into the field: as a vector. -/
def valsAt (n : Nat) (l : List OnBytes.E) : Fin n → Cb.Gl.E :=
  fun i => toE ((padTo n l).getD i.1 OnBytes.zeroE).triple

/-! ## 2 What is said, shown and yielded -/

/-- What the move says, as a view shows it: the words of value plus coin, one by one. -/
theorem said_scalars (n : Nat) (l : List OnBytes.E) (c : Cs ⟨0, n⟩) :
    (sayE (addL (padTo n l) (coinsE c))).vals.map Said.got =
      List.ofFn fun i => .e (ofE (valsAt n l i + c.e i)) := by
  unfold coinsE
  rw [addL_ofFn n _ _ (padTo_len n l)]
  unfold sayE
  show ((List.ofFn _).map _).map Said.got = _
  rw [List.map_ofFn, List.map_ofFn]
  refine congrArg List.ofFn (funext fun i => ?_)
  show Fmt.ItemValue.e (ofE (toE (OnBytes.addE _ _).triple)) = _
  rw [OnBytes.addE_triple, OnBytes.Slice.toE_addE]
  show Fmt.ItemValue.e (ofE (_ + toE (ofE (c.e i)))) = _
  rw [OnBytes.Slice.toE_ofE]
  rfl

/-- It has the shape of a round that states n elements and no oracle message. -/
theorem fits_scalars (n : Nat) (l : List OnBytes.E) (c : Cs ⟨0, n⟩) (d : Fmt.DeclaredRound)
    (h : d.items.filter (· != .root) = List.replicate n .e) :
    (sayE (addL (padTo n l) (coinsE c))).fits d [] = true := by
  have h1 : (sayE (addL (padTo n l) (coinsE c))).vals.map (fun v => itemOf v.got) =
      List.replicate n .e := by
    have h2 := congrArg (List.map itemOf) (said_scalars n l c)
    rw [List.map_map, List.map_ofFn] at h2
    rw [← List.ofFn_const]
    exact h2
  unfold Sending.fits
  rw [h, h1]
  simp [sayE]

/-- What the simulator yields: the words of its coins. -/
theorem tells_scalars (φ : Face V W Pb) (j n : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))
    (a : Addr) (p : Part V W X) (c : Cs ⟨0, n⟩) (w : W) (front : Before) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) :
    Member.tells ⟨j, rs, p, scalarsSim a n⟩ φ c w front ds asks = scalarsAt c.e := by
  show some [(⟨(coinsE c).map fun x => .e x.triple, []⟩ : Shown)] = _
  unfold coinsE scalarsAt
  rw [List.map_ofFn]
  rfl

/-- Conditional on h1 and h2, which are the premise hrs taken apart: what the part shows, seated at
whatever lens: the words of value plus coin. -/
theorem shows_scalars (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (j n : Nat)
    (r : Fmt.DeclaredRound × List Oracle) (a : Addr) (name : String)
    (vals : W' → Front Y → List OnBytes.E)
    (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X)
    (h1 : r.1.items.filter (· != .root) = List.replicate n .e) (h2 : r.2 = [])
    (c : Cs ⟨0, 0⟩) (sp : CsAll [(name, (⟨0, n⟩ : Due))]) (ca : Unit) (m : Mid W X)
    (R : Fmt.Drawn) (asks : List (List (List Nat))) :
    σ.shows φ ⟨j, [r], (scalarsPart name n vals : Part V' W' Y).lift see wit get set,
        scalarsSim a n⟩ (c, sp, ca) m [R] asks =
      scalarsAt (valsAt n (vals (wit m.st.input) ⟨m.st.heard, get m.st.own, m.shown⟩) +
        sp.1.e) := by
  obtain ⟨d, os⟩ := r
  subst h2
  have h : play (((scalarsPart name n vals : Part V' W' Y).lift see wit get set).steps σ.block.name
      ⟨σ.block.place, j⟩ [(d, [])] (φ.sees m.st.input) (c, sp, ca)) [R] [] m =
      .ok ([⟨σ.block.name, σ.block.place, j, true,
        (sayE (addL (padTo n (vals (wit m.st.input) ⟨m.st.heard, get m.st.own, m.shown⟩))
          (coinsE sp.1))).vals.map Said.got, [], R⟩], _) :=
    play_one
      (z := sayE (addL (padTo n (vals (wit m.st.input) ⟨m.st.heard, get m.st.own, m.shown⟩))
        (coinsE sp.1)))
      (fun _ _ => rfl) (fun _ _ => bindNone _) rfl rfl (fits_scalars n _ sp.1 d h1)
  unfold Side.shows
  show ((play (((scalarsPart name n vals : Part V' W' Y).lift see wit get set).steps σ.block.name
    ⟨σ.block.place, j⟩ [(d, [])] (φ.sees m.st.input) (c, sp, ca)) [R] [] m).toOption.map
      fun y => shownOf y.1 asks) = _
  rw [h]
  show some [(⟨(sayE _).vals.map Said.got, []⟩ : Shown)] = _
  rw [said_scalars]
  rfl

/-! ## 3 `ExactMember` -/

/-- Conditional on hrs. **`ExactMember` at one round that sends n scalars, each as its value plus a
mask entry, the part seated by `Part.lift` at whatever see, wit, get and set.** -/
theorem scalarsPart_exact_lift (φ : Face V W Pb) (σ : Side S Cl V W X Pb)
    (chain firstTree : Nat)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (j n : Nat) (rs : List (Fmt.DeclaredRound × List Oracle)) (a : Addr) (name : String)
    (vals : W' → Front Y → List OnBytes.E)
    (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hrs : statedOf rs = [(List.replicate n .e, [])]) :
    ExactMember φ σ chain firstTree On bud
      ⟨j, rs, (scalarsPart name n vals : Part V' W' Y).lift see wit get set, scalarsSim a n⟩ := by
  match rs, hrs with
  | [r], hrs =>
    have h0 : (r.1.items.filter (· != .root), r.2) = (List.replicate n Fmt.Item.e, []) :=
      List.head_eq_of_cons_eq hrs
    have h1 := congrArg Prod.fst h0
    have h2 := congrArg Prod.snd h0
    intro ca m front ds asks _ _ hd _ _ _
    have hd' : drawsFit [r.1] ds = true := hd
    obtain ⟨R, rfl, -⟩ := drawsFit_one hd'
    refine Eq.trans (map_unif_by_equiv ((eq0E name n).trans (Equiv.addLeft
      (valsAt n (vals (wit m.st.input) ⟨m.st.heard, get m.st.own, m.shown⟩))))
      scalarsAt _ fun c =>
        shows_scalars φ σ j n r a name vals see wit get set h1 h2 c.1 c.2 ca m R asks)
      (Eq.symm ?_)
    exact map_unif_by_equiv (eqE n) scalarsAt _
      fun c => tells_scalars φ j n [r] a _ c m.st.input front [R] asks
  | [], hrs => simp [statedOf] at hrs
  | _ :: _ :: _, hrs => simp [statedOf] at hrs

/-- Conditional on hrs. **`ExactMember` at one round that sends n scalars, each as its value plus a
mask entry: the bare part.** -/
theorem scalarsPart_exact (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (chain firstTree : Nat)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (j n : Nat) (rs : List (Fmt.DeclaredRound × List Oracle)) (a : Addr) (name : String)
    (vals : W → Front X → List OnBytes.E)
    (hrs : statedOf rs = [(List.replicate n .e, [])]) :
    ExactMember φ σ chain firstTree On bud ⟨j, rs, scalarsPart name n vals, scalarsSim a n⟩ :=
  scalarsPart_exact_lift φ σ chain firstTree On bud j n rs a name vals id id id (fun x _ => x) hrs

end ProofFile.Honest.Small

#print axioms ProofFile.Honest.Small.bindNone
#print axioms ProofFile.Honest.Small.addL_ofFn
#print axioms ProofFile.Honest.Small.padTo_len
#print axioms ProofFile.Honest.Small.said_scalars
#print axioms ProofFile.Honest.Small.fits_scalars
#print axioms ProofFile.Honest.Small.tells_scalars
#print axioms ProofFile.Honest.Small.shows_scalars
#print axioms ProofFile.Honest.Small.scalarsPart_exact_lift
#print axioms ProofFile.Honest.Small.scalarsPart_exact
#print axioms ProofFile.Honest.Small.eqE
#print axioms ProofFile.Honest.Small.eq0E
#print axioms ProofFile.Honest.Small.scalarsAt
#print axioms ProofFile.Honest.Small.valsAt
