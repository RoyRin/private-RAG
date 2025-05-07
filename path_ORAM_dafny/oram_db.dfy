datatype Block = Block(addr: int, data: string)


class Database {
    var buckets: seq<seq<Block>>

    constructor(databaseSize: nat, bucketSize: nat)
        requires databaseSize >= 1
        requires bucketSize >= 1
        ensures |buckets| == databaseSize
        ensures forall bucket :: bucket in buckets ==> |bucket| == bucketSize
    {
        buckets := [];
        new;
        var i := 0;
        while i < databaseSize
            invariant |buckets| == i
            invariant i <= databaseSize
            invariant forall bucket :: bucket in buckets ==> |bucket| == bucketSize
        {
            var bucket := [];
            var j := 0; 
            while j < bucketSize
                invariant |bucket| == j
                invariant j <= bucketSize
                invariant |buckets| == i
                invariant forall bucket :: bucket in buckets ==> |bucket| == bucketSize
            {
                bucket := bucket + [Block(-1, "")];
                j := j + 1;
            }
            buckets := buckets + [bucket];
            i := i + 1;
        }
    }

    method ReadBucket(bucket_idx: nat) returns (blocks: seq<Block>)
        requires 0 <= bucket_idx < |buckets|
        ensures blocks == buckets[bucket_idx]
    {
        blocks := buckets[bucket_idx];
    }

    method WriteBucket(bucket_idx: nat, blocks: seq<Block>)
        requires 0 <= bucket_idx < |buckets|
        modifies this`buckets
        ensures 0 <= bucket_idx < |buckets|
        ensures buckets[bucket_idx] == blocks
        ensures |buckets| == |old(buckets)|
    {
        buckets := buckets[bucket_idx := blocks];
    }
}
