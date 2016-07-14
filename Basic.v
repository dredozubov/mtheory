Inductive Pitch := pA | pB | pC | pD | pE | pF | pG.

Require Import Coq.Init.Datatypes.

Set Implicit Arguments.

Inductive Fin : nat -> Set :=
  | FZ : forall n, Fin (S n)
  | FS : forall n, Fin n -> Fin (S n).

Inductive PitchName : Set :=
  | nCb | nC | nCs
  | nDb | nD | nDs
  | nEb | nE | nEs
  | nFb | nF | nFs
  | nGb | nG | nGs
  | nAb | nA | nAs
  | nBb | nB | nBs.

Inductive PitchClass : Set :=
  | Cb | C | Cs
  | Db | D | Ds
  | Eb | E
  | Fb | F | Fs
  | Gb | G | Gs
  | Ab | A | As
  | Bb | B.

Inductive PitchNumber :=
  | pn1
  | pn2
  | pn3
  | pn4
  | pn5
  | pn6
  | pn7
  | pn8
  | pn9
  | pn10
  | pn11
  | pn12.

Class ToPitchNumber (A : Set) :=
  toPitchNumber : A -> PitchNumber.

Instance pitchClassToPitchNumber : ToPitchNumber PitchClass :=
  { toPitchNumber pc :=
      match pc with
      | Cb => pn12
      | C  => pn1
      | Cs => pn2
      | Db => pn2
      | D  => pn3
      | Ds => pn4
      | Eb => pn4
      | E  => pn5
      | Fb => pn5
      | F  => pn6
      | Fs => pn7
      | Gb => pn7
      | G  => pn8
      | Gs => pn9
      | Ab => pn9
      | A  => pn10
      | As => pn11
      | Bb => pn11
      | B  => pn12
    end }.

Instance pitchNameToPitchNumber : ToPitchNumber PitchName :=
  { toPitchNumber pc :=
      match pc with
      | nCb => pn12
      | nC  => pn1
      | nCs => pn2
      | nDb => pn2
      | nD  => pn3
      | nDs => pn4
      | nEb => pn4
      | nE  => pn5
      | nEs => pn6
      | nFb => pn5
      | nF  => pn6
      | nFs => pn7
      | nGb => pn7
      | nG  => pn8
      | nGs => pn9
      | nAb => pn9
      | nA  => pn10
      | nAs => pn11
      | nBb => pn11
      | nB  => pn12
      | nBs => pn1
    end }.

Inductive Character : Set := maj | min.

Inductive Key (pc : PitchClass) (c : Character) : Set :=
  | key : Key pc c.

Inductive MajorMode :=
  | Ionian
  | Dorian
  | Phrygian
  | Lydian
  | Mixolydian
  | Aeolian
  | Locrian.

Inductive RelativeInterval :=
  | Unison
  | Second
  | Third
  | Fourth
  | Fifth
  | Sixth
  | Seventh
  | Octave.

Inductive Diatonic :=
  | tone
  | halftone.

Inductive Interval :=
  | i : Character -> RelativeInterval -> Interval.

Require Import Coq.Lists.List.

Open Scope list_scope.

Import ListNotations.

Definition strip (pc : PitchClass) : Pitch :=
  match pc with
    | Cb => pC
    | C  => pC
    | Cs => pC
    | Db => pD
    | D  => pD
    | Ds => pD
    | Eb => pE
    | E  => pE
    | Fb => pF
    | F  => pF
    | Fs => pF
    | Gb => pG
    | G  => pG
    | Gs => pG
    | Ab => pA
    | A  => pA
    | As => pA
    | Bb => pB
    | B  => pB
  end.

Definition next (pc : Pitch) : Pitch :=
  match pc with
    | pC => pD
    | pD => pE
    | pE => pF
    | pF => pG
    | pG => pA
    | pA => pB
    | pB => pC
  end.

Definition modeRecipe (m : MajorMode) : list Diatonic :=
  match m with
    | Ionian     => [ tone ; tone ; halftone ; tone ; tone ; tone ; halftone ]
    | Dorian     => [ tone ; halftone ; tone ; tone ; tone ; halftone ; tone ]
    | Phrygian   => [ halftone ; tone ; tone ; tone ; halftone ; tone ; tone ]
    | Lydian     => [ tone ; tone ; tone ; halftone ; tone ; tone ; halftone ]
    | Mixolydian => [ tone ; tone ; halftone ; tone ; tone ; halftone ; tone ]
    | Aeolian    => [ tone ; halftone ; tone ; tone ; halftone ; tone ; tone ]
    | Locrian    => [ halftone ; tone ; tone ; halftone ; tone ; tone ; tone ]
  end.
