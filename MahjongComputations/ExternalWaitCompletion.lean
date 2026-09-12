import MahjongComputations.Common
import Std.Sync.Mutex

/-!
# External wait-completion records

Direct derivations are encoded as fixed-width byte records before bucket aggregation.
-/

namespace MahjongComputations.ExternalWaitCompletion

open MahjongComputations

/-- One decoded record written by the external canonical-derivation pipeline. -/
structure Record where
  tiles : List Tile
  completion : WaitCompletion
deriving BEq, DecidableEq, Repr

private def winningComponentAlphabet : List WinningComponent :=
  Tile.all.map WinningComponent.pair ++
    MentsuCandidate.candidates.map fun mentsu => (.inr mentsu : WinningComponent)

/-- Number of bytes in one record for a hand with `mentsuCount` completed mentsu. -/
def recordWidth (mentsuCount : Nat) : Nat :=
  standardTenpaiHandSize mentsuCount + 1 + (mentsuCount + 1)

private def encodeIndex {α : Type} [BEq α] (alphabet : List α) (value : α) : UInt8 :=
  UInt8.ofNat (alphabet.idxOf value)

private def decodeIndex {α : Type} (alphabet : List α) (value : Nat) : Option α :=
  alphabet[value]?

/-- Encode a normalized hand and completion into one fixed-width record. -/
def encode (mentsuCount : Nat) (record : Record) : Option ByteArray := do
  guard (record.tiles.length == standardTenpaiHandSize mentsuCount)
  let components := record.completion.winningComponents.toList
  guard (components.length == mentsuCount + 1)
  let bytes := record.tiles.foldl
    (fun bytes tile => bytes.push (encodeIndex Tile.all tile)) ByteArray.empty
  let bytes := bytes.push (encodeIndex Tile.all record.completion.wait)
  return components.foldl
    (fun bytes component => bytes.push (encodeIndex winningComponentAlphabet component)) bytes

/-- Decode one fixed-width record, rejecting malformed lengths and out-of-range indices. -/
def decode (mentsuCount : Nat) (bytes : ByteArray) : Option Record := do
  guard (bytes.size == recordWidth mentsuCount)
  let values := bytes.data.toList.map UInt8.toNat
  let handSize := standardTenpaiHandSize mentsuCount
  let tiles ← (values.take handSize).mapM (decodeIndex Tile.all)
  let waitIndex ← values[handSize]?
  let wait ← decodeIndex Tile.all waitIndex
  let components ← (values.drop (handSize + 1)).mapM (decodeIndex winningComponentAlphabet)
  guard (components.length == mentsuCount + 1)
  return {
    tiles
    completion := { wait, winningComponents := CanonicalWinningComponents.ofList components }
  }

private def formatMagic : ByteArray := "MJWC".toUTF8
private def formatVersion : UInt8 := 1
private def headerWidth : Nat := 8

private def header (mentsuCount : Nat) : Option ByteArray := do
  guard (mentsuCount < 256)
  guard (recordWidth mentsuCount < 256)
  return (formatMagic.push formatVersion)
    |>.push (UInt8.ofNat mentsuCount)
    |>.push (UInt8.ofNat (recordWidth mentsuCount))
    |>.push 0

private def validateHeader (mentsuCount : Nat) (bytes : ByteArray) : Bool :=
  header mentsuCount == some bytes

/-- Buffered writer for one external bucket file. -/
structure Writer where
  handle : IO.FS.Handle
  mentsuCount : Nat
  buffer : IO.Ref ByteArray
  bufferCapacity : Nat

/-- Open a bucket writer and emit its header. -/
def Writer.open (path : System.FilePath) (mentsuCount : Nat)
    (bufferCapacity : Nat := 65536) : IO Writer := do
  let some fileHeader := header mentsuCount
    | throw (IO.userError s!"unsupported mentsu count: {mentsuCount}")
  let handle ← IO.FS.Handle.mk path .write
  handle.write fileHeader
  let buffer ← IO.mkRef ByteArray.empty
  return { handle, mentsuCount, buffer, bufferCapacity := max 1 bufferCapacity }

private def Writer.flush (writer : Writer) : IO Unit := do
  let bytes ← writer.buffer.get
  unless bytes.isEmpty do
    writer.handle.write bytes
    writer.buffer.set ByteArray.empty

/-- Flush and close a bucket writer. -/
def Writer.close (writer : Writer) : IO Unit := do
  writer.flush
  writer.handle.flush

/-- Append one record, flushing the in-memory byte buffer when it reaches its capacity. -/
def Writer.append (writer : Writer) (record : Record) : IO Unit := do
  let some encoded := encode writer.mentsuCount record
    | throw (IO.userError "invalid external wait-completion record")
  let bytes ← writer.buffer.modifyGet fun bytes =>
    let updated := bytes ++ encoded
    (updated, updated)
  if bytes.size >= writer.bufferCapacity then
    writer.flush

/-- Open a new bucket, write its versioned header, and flush buffered records on exit. -/
def withWriter {α : Type} (path : System.FilePath) (mentsuCount : Nat)
  (bufferCapacity : Nat := 65536)
    (action : Writer → IO α) : IO α := do
  let writer ← Writer.open path mentsuCount bufferCapacity
  try
    action writer
  finally
    writer.close

/-- Concurrent writers for hash-partitioned external bucket files. -/
structure BucketSet where
  directory : System.FilePath
  bucketCount : Nat
  firstBucket : Std.Mutex Writer
  remainingBuckets : List (Std.Mutex Writer)

/-- Stable path for one bucket file. -/
def bucketPath (directory : System.FilePath) (bucketIndex : Nat) : System.FilePath :=
  directory / s!"bucket-{bucketIndex}.bin"

/-- Paths in deterministic bucket-index order. -/
def BucketSet.paths (buckets : BucketSet) : List System.FilePath :=
  (List.range buckets.bucketCount).map (bucketPath buckets.directory)

/-- Create and truncate all files in a shared bucket set. -/
def BucketSet.open (directory : System.FilePath) (mentsuCount bucketCount : Nat)
    (bufferCapacity : Nat := 65536) : IO BucketSet := do
  IO.FS.createDirAll directory
  let count := max 1 bucketCount
  let newBucket (index : Nat) : IO (Std.Mutex Writer) := do
    let writer ← Writer.open (bucketPath directory index) mentsuCount bufferCapacity
    Std.Mutex.new writer
  let firstBucket ← newBucket 0
  let remainingBuckets ← (List.range (count - 1)).mapM fun index => newBucket (index + 1)
  return { directory, bucketCount := count, firstBucket, remainingBuckets }

private def BucketSet.bucketFor (buckets : BucketSet) (key : Nat) : Std.Mutex Writer :=
  (buckets.firstBucket :: buckets.remainingBuckets).getD
    (key % buckets.bucketCount) buckets.firstBucket

/-- Append a record to the bucket selected by its normalized hand key. -/
def BucketSet.append (buckets : BucketSet) (record : Record) : IO Unit :=
  (buckets.bucketFor (tileMultisetKey record.tiles)).atomically do
    let writer ← get
    writer.append record

/-- Flush and close every file in the bucket set. -/
def BucketSet.close (buckets : BucketSet) : IO Unit :=
  (buckets.firstBucket :: buckets.remainingBuckets).forM fun bucket =>
    bucket.atomically do
      let writer ← get
      writer.close

/-- Open a shared bucket set and close every file on exit. -/
def withBucketSet {α : Type} (directory : System.FilePath) (mentsuCount bucketCount : Nat)
    (bufferCapacity : Nat := 65536) (action : BucketSet → IO α) : IO α := do
  let buckets ← BucketSet.open directory mentsuCount bucketCount bufferCapacity
  try
    action buckets
  finally
    buckets.close

private partial def readRecords {α : Type} (handle : IO.FS.Handle) (mentsuCount : Nat)
    (state : α) (f : α → Record → IO α) : IO α := do
  let bytes ← handle.read (USize.ofNat (recordWidth mentsuCount))
  if bytes.isEmpty then
    return state
  let some record := decode mentsuCount bytes
    | throw (IO.userError "truncated or malformed external wait-completion record")
  readRecords handle mentsuCount (← f state record) f

/-- Validate and stream all records from one external bucket file. -/
def foldFile {α : Type} (path : System.FilePath) (mentsuCount : Nat) (init : α)
    (f : α → Record → IO α) : IO α :=
  IO.FS.withFile path .read fun handle => do
    let fileHeader ← handle.read (USize.ofNat headerWidth)
    unless validateHeader mentsuCount fileHeader do
      throw (IO.userError "invalid external wait-completion bucket header")
    readRecords handle mentsuCount init f

private def recordSortKey (mentsuCount : Nat) (record : Record) : Nat :=
  (encode mentsuCount record).getD ByteArray.empty |>.data.foldl
    (fun key byte => key * 128 + byte.toNat + 1) 0

/-- Put a group's completions in the stable order defined by the external encoding. -/
def normalizeGroup (mentsuCount : Nat) (group : WaitCompletionGroup) : WaitCompletionGroup :=
  { group with
    completions := group.completions.mergeSort fun first second =>
      decide (recordSortKey mentsuCount { tiles := group.tiles, completion := first } ≤
        recordSortKey mentsuCount { tiles := group.tiles, completion := second }) }

/-- Read and deduplicate the wait completions for every hand in one bucket. -/
def readGroups (path : System.FilePath) (mentsuCount : Nat) : IO (List WaitCompletionGroup) := do
  let groups ← foldFile path mentsuCount (∅ : Std.HashMap Nat WaitCompletionGroup)
    fun groups record =>
      let key := tileMultisetKey record.tiles
      let updated := match groups.get? key with
        | none => { tiles := record.tiles, completions := [record.completion] }
        | some existing =>
            { existing with
              completions := insertCompletion record.completion existing.completions }
      pure (groups.insert key updated)
  return groups.values.map (normalizeGroup mentsuCount)

end MahjongComputations.ExternalWaitCompletion
