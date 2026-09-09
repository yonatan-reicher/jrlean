module
import Jrlean.Of
public import Jrlean.Wav
public import Jrlean.Wave

namespace Jrlean

/-
API:

A song is a beat sequence.
A beat sequence can be made up of a single beat, two beat sequences one after
the other, or two beat sequences at the same time.
A song has a tempo. The duration of a beat is decided by a tempo.
A beat itself is made up of a sequence of sub-beats.
A sequence of sub-beats is either a single note, two sequences yada yada or yada
yada.

A note is made out of a sound wave
-/

@[expose]
public section

structure Note where
  /-- The number of periods per second a sound has when it rings this note. -/
  frequency : Float
  deriving DecidableEq, Inhabited, Repr

structure Bpm where 
  bpm : Float
  deriving DecidableEq, Inhabited, Repr

def Bpm.beatsPerSecond (b : Bpm) := b.bpm / 60.0
def Bpm.secondsPerBeat (b : Bpm) := 1.0 / b.beatsPerSecond

structure Sound where
  note : Note
  wave : Wave
  duration : Float
  dropOff : Bool
  easeIn : Bool
  deriving DecidableEq, Inhabited, Repr
structure SubBeat where
  sound : Sound
  deriving DecidableEq, Inhabited, Repr
structure Beat where
  subBeats : Array SubBeat
  deriving DecidableEq, Inhabited, Repr
structure Song where
  beats : Array Beat
  bpm : Bpm
  deriving DecidableEq, Inhabited, Repr

instance {n} [HMul Float n Float] : HMul Note n Note where
  hMul | { frequency := f }, x => { frequency := f * x }

def Note.A4 : Note := .mk 440
def Note.C4 : Note := A4 * (2 ^ (-9.0 / 12))
def Note.D4 : Note := C4 * (2 ^ (2.0 / 12))
def Note.E4 : Note := C4 * (2 ^ (4.0 / 12))
def Note.F4 : Note := C4 * (2 ^ (5.0 / 12))
def Note.G4 : Note := C4 * (2 ^ (7.0 / 12))
-- def Note.A4 : Note := ...
def Note.B4 : Note := C4 * (2 ^ (11.0 / 12))
def Note.C5 : Note := C4 * 2.0

instance {n} [HMul Note n Note] : HMul Sound n Sound where
  hMul sound a := { sound with note := sound.note * a }

abbrev Time := Float
def Sound.sample (s : Sound) (t : Time) : Float :=
  -- Calculate x ∈ [0, 1), the scaled position in the period of the wave.
  let pastPeriods := (t * s.note.frequency).floor
  let t₀ := t * s.note.frequency - pastPeriods
  if ¬(0 ≤ t₀ ∧ t₀ < 1) then panic! "this should not happen!" else
    let dropOffMultiplier := if s.dropOff then 1 - t / s.duration else 1
    let easeInMultiplier := if s.easeIn then t / s.duration else 1
    let fixAfterBoth := if s.dropOff && s.easeIn then 2 else 1
    let retFloat := s.wave.sample t₀ * dropOffMultiplier * easeInMultiplier * fixAfterBoth
    retFloat

abbrev NonEmptyArray α := { a : Array α // not a.isEmpty }
def NonEmptyArray.singleton (a : α) : NonEmptyArray α := ⟨#[a], Bool.not_eq_eq_eq_not.mpr rfl⟩

instance {α} [Inhabited α] : Inhabited (NonEmptyArray α) where
  default := .singleton default

structure Arrangement where
  sounds : Array (Float × NonEmptyArray Sound)
  duration : Float
  deriving DecidableEq, Inhabited, Repr

def Arrangement.timeUntilLastSound (a : Arrangement) : Float :=
  Array.sum of a.sounds.map Prod.fst

def Arrangement.delay (x : Float) (a : Arrangement) : Arrangement :=
  { a with sounds := sounds a.sounds }
where
  sounds (a : Array of Float × NonEmptyArray Sound) :=
    if h : a.size = 0
    then a
    else
      let (delay, sound) := a[0]
      a.set 0 (delay + x, sound)

def Arrangement.append (a b : Arrangement) : Arrangement where
  sounds := a.sounds ++ (b.delay of a.duration - a.timeUntilLastSound).sounds
  duration := a.duration + b.duration

def Beat.arrange (duration : Float) (b : Beat) : Arrangement :=
  b.subBeats.foldl fold init |> finalize
where
  init : Array _ × Bool := (#[], true)
  fold := λ (a, isFirstFrame) sb => (a.push (delay isFirstFrame, .singleton sb.sound), false)
  delay
    | true => 0
    | false => duration / b.subBeats.size.toFloat
  finalize := fun (sounds, _) => { sounds, duration }

def Song.duration (s : Song) : Float := s.bpm.secondsPerBeat * s.beats.size.toFloat

def Song.arrange (s : Song) : Arrangement :=
  s.beats.foldl fold init
where
  init := (default : Arrangement)
  fold a b := a.append of b.arrange s.bpm.secondsPerBeat

structure ArrangementCompiler.CurrentlyPlaying where
  sound : Sound
  frame : Nat
  deriving DecidableEq, Inhabited, Repr

structure ArrangementCompiler.ToPlay where
  sounds : NonEmptyArray Sound
  delay : Nat
  deriving DecidableEq, Inhabited, Repr

structure ArrangementCompiler where
  arrangement : Arrangement
  toPlay : List ArrangementCompiler.ToPlay
  frames : Nat
  framesPerSecond : Float
  frame : Option of Fin frames
  currentlyPlaying : Array ArrangementCompiler.CurrentlyPlaying
  deriving DecidableEq, Inhabited, Repr

def Arrangement.toCompiler (a : Arrangement) (framesPerSecond : Float) : ArrangementCompiler :=
  let frames := (a.duration * framesPerSecond).toUInt64.toNat
  { arrangement := a
    toPlay := toPlay a
    frames := frames
    frame := firstFrame frames
    framesPerSecond,
    currentlyPlaying := #[] }
where
  firstFrame : (frames : Nat) → Option $ Fin frames
    | 0 => none
    | _ + 1 => some 0
  toPlay a :=
    a.sounds.map (λ (delay, sound) => ⟨sound, (delay * framesPerSecond).round.toUInt64.toNat⟩)
    |>.toList

def ArrangementCompiler.isDone (a : ArrangementCompiler) : Bool := a.frame.isNone

def ArrangementCompiler.readFrame {m} [Monad m] [MonadStateOf ArrangementCompiler m]
    : m (Option UInt8) := do
  if isDone (← get) then return none
  -- Decide if we need to start playing the next sounds
  let newlyPlaying ← popSoundsToStartPlaying
  if let some x := newlyPlaying then startPlaying x
  -- Sample the currently playing sounds
  let sample ← sample
  -- Filter out finished currently playing sounds
  updateCurrentlyPlaying
  updateFrame
  return some sample
where
  popSoundsToStartPlaying := do
    let a ← get
    match a.toPlay with
    | [] => return none
    | { sounds, delay := 0 } :: tail =>
      set { a with toPlay := tail }
      return some sounds
    | { sounds, delay := delay' + 1 } :: tail =>
      set { a with toPlay := { sounds, delay := delay' } :: tail }
      return none
  startPlaying newlyPlaying :=
    let newlyPlaying : Array CurrentlyPlaying := newlyPlaying.val.map (⟨·, 0⟩)
    modify fun a => { a with currentlyPlaying := a.currentlyPlaying ++ newlyPlaying }
  sample := do
    let a ← get
    let sampleFloat := Array.sum of a.currentlyPlaying.map λ { sound, frame } =>
      let t := frame.toFloat / a.framesPerSecond
      sound.sample t
    return sampleFloat * 255 |>.round.toUInt8
  updateCurrentlyPlaying := modify λ a =>
    { a with
      currentlyPlaying := a.currentlyPlaying.filterMap fun { sound, frame } =>
        let t := frame.toFloat / a.framesPerSecond
        if sound.duration <= t
        then none
        else some { sound, frame := frame + 1 } }
  updateFrame := modify λ a => 
    match a.frame with
    | some f => { a with frame := f.addNat? 1 }
    | none => a

def ArrangementCompiler.compileRef (a : IO.Ref ArrangementCompiler) : IO.FS.Stream where
  isTty := pure false
  flush := pure ()
  write _ := unsupported
  putStr _ := unsupported
  getLine := unsupported
  read n := show IO _ from do
    have : MonadStateOf ArrangementCompiler IO := a.toMonadStateOf
    let mut ret := ByteArray.empty
    for _ in [0:n.toNat] do
      match (← readFrame) with
      | none => break
      | some c => ret := ret.push c
    return ret
where
  unsupported {α} : IO α := throw $ .userError "cannot write to an arrangement stream"

def ArrangementCompiler.compile (a : ArrangementCompiler) : IO IO.FS.Stream :=
  compileRef <$> IO.mkRef a

def song : Song where
  beats := notes.map myBeat
  bpm := Bpm.mk 90
where
  myBeat (notes : Array Note) : Beat := ⟨notes.map mySubBeat⟩
  mySubBeat (note : Note) : SubBeat :=
    ⟨{
      note := note * 0.5,
      wave := .sin
      duration := 0.34
      dropOff := true
      easeIn := true
    }⟩
  notes : Array of Array Note := #[
    #[.C4],
    #[.D4],
    #[.E4],
    #[.C4],
    #[.D4],
    #[.D4],
    #[.F4],
    #[.E4, .D4, .E4],
  ]

#eval song.arrange.sounds

#eval do
  let fps : Float := 44100
  let duration : Float := song.duration
  let frames : Nat := fps * duration |>.toUInt64.toNat
  let s ← (song.arrange |>.toCompiler fps).compile
  let b ← s.readBinToEnd
  playWavFile =<< IO.FS.Stream.ofHandle <$> mkWavFile frames fps fun i => b[i]!

#evaj do
  let framesPerSecond := 4e4
  let duration : Float := 0.5
  let frames := (duration * framesPerSecond * 5).toUInt64.toNat
  let sound := {
    duration
    note := Note.C4
    dropOff := true
    easeIn := true
    wave := .sin
    : Sound
  }
  playWavFile
  =<< IO.FS.Stream.ofHandle
  <$> mkWavFile frames framesPerSecond λ i =>
    let t := Float.ofNat i / framesPerSecond
    let i := t / duration
    let bass := sound * 0.25 * 1.75 |> (λ s : Sound => { s with duration := duration * 4, easeIn := false })
    let r :=
      0.75 * bass.sample t +
      if i < 1 then
        sound.sample t
      else if i < 2 then
        sound.sample (t - duration)
        + (sound * (5.0 / 4)).sample (t - duration)
      else if i < 3 then
        (sound * 1.5).sample (t - 2 * duration)
        + (sound * (5.0 / 4) * 1.5).sample (t - 2 * duration)
      else if i < 4 then
        (sound * 1.25).sample (t - 3 * duration)
        + (sound * (5.0 / 4) * 1.25).sample (t - 3 * duration)
      else
        0.5 * (
          (sound).sample (t - 4 * duration)
          + (sound * (5.0 / 4)).sample (t - 4 * duration)
          + (sound * (8.0 / 4)).sample (t - 4 * duration)
        )
    r * 255 |>.toUInt8

