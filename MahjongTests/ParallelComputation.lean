import MahjongComputations.Parallel

namespace MahjongTests.ParallelComputation

open MahjongComputations
open WaitCompletionFinder

private def testHand : List Tile := manzu [0, 1, 2, 3]
private def otherHand : List Tile := manzu [3]

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def run : IO UInt32 := do
  let cache ← SharedWaitCoreCache.new
  let tasks ← (List.range 8).mapM fun _ =>
    BaseIO.asTask (do
      let threadId ← IO.getTID
      let result ← cache.lookup testHand
      return (threadId, result)) Task.Priority.dedicated
  let taskResults ← tasks.mapM fun task => BaseIO.toIO (IO.wait task)
  let threadIds := taskResults.map Prod.fst |>.eraseDups
  let results := taskResults.map Prod.snd
  ensure (threadIds.length > 1) s!"worker tasks used only one thread: {threadIds}"
  ensure (results.all fun result => result == results.head!)
    "concurrent cache lookups returned different results"
  let stats ← cache.stats
  ensure (stats == { hits := 7, misses := 1, entries := 1 })
    s!"unexpected concurrent cache stats: {repr stats}"

  let repeated ← cache.lookup testHand
  ensure (repeated == results.head!) "ready cache lookup changed its result"
  let stats ← cache.stats
  ensure (stats == { hits := 8, misses := 1, entries := 1 })
    s!"unexpected ready cache stats: {repr stats}"

  discard <| cache.lookup otherHand
  let stats ← cache.stats
  ensure (stats == { hits := 8, misses := 2, entries := 2 })
    s!"unexpected distinct-key cache stats: {repr stats}"
  IO.println "parallel wait-core cache tests passed"
  return 0

end MahjongTests.ParallelComputation

def main : IO UInt32 :=
  MahjongTests.ParallelComputation.run