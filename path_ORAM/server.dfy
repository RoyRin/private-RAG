class Block {
    var addr: int
    var data: string
    
    constructor(addr: int, data: string)
        requires addr >= -1
        ensures this.addr == addr
        ensures this.data == data
    {
        this.addr := addr;
        this.data := data;
    }
}


class Bucket {
    var blocks: seq<Block>

    constructor(bucketSize: nat)
        requires bucketSize >= 1
        ensures |blocks| == bucketSize
    {
        blocks := [];
        new;
        var i := 0;
        while i < bucketSize
            invariant |blocks| == i
            invariant i <= bucketSize
        {
            var newBlock := new Block(-1, "");
            blocks := blocks + [newBlock];
            i := i + 1;
        }
    }
}


class Database {
    var buckets: seq<Bucket>
    var accessLog: seq<(string, nat)>

    constructor(databaseSize: nat, bucketSize: nat)
        requires databaseSize >= 1
        requires bucketSize >= 1
        ensures |buckets| == databaseSize
        ensures forall bucket :: bucket in buckets ==> |bucket.blocks| == bucketSize
    {
        buckets := [];
        accessLog := [];
        new;
        var i := 0;
        while i < databaseSize
            invariant |buckets| == i
            invariant i <= databaseSize
            invariant forall bucket :: bucket in buckets ==> |bucket.blocks| == bucketSize
        {
            var newBucket := new Bucket(bucketSize);
            buckets := buckets + [newBucket];
            i := i + 1;
        }
    }

    method ReadBucket(bucket: nat) returns (blocks: seq<Block>)
        requires 0 <= bucket < |buckets|
        modifies this`accessLog
        ensures blocks == buckets[bucket].blocks
        ensures accessLog == old(accessLog) + [("R", bucket)]
    {
        blocks := buckets[bucket].blocks;
        accessLog := accessLog + [("R", bucket)];
    }

    method WriteBucket(bucket: nat, blocks: seq<Block>)
        requires 0 <= bucket < |buckets|
        modifies this.buckets, this`accessLog
        ensures buckets[bucket].blocks == blocks
        ensures buckets == old(buckets)
        ensures accessLog == old(accessLog) + [("W", bucket)]
    {
        buckets[bucket].blocks := blocks;
        accessLog := accessLog + [("W", bucket)];
    }

    method WriteAccessLog()
    {
        print accessLog;
    }

    method ClearAccessLog()
        modifies this`accessLog
        ensures |accessLog| == 0
    {
        accessLog := [];
    }
}
