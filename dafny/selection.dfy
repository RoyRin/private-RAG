

predicate sorted(a: array<int>)
  reads a
{
  forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}
method BinarySearch(a: array<int>, value: int) returns (index: int)
  requires 0 <= a.Length && sorted(a)
  ensures 0 <= index ==> index < a.Length && a[index] == value
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
{
  var low, high := 0, a.Length;
  while low < high
    invariant 0 <= low <= high <= a.Length
    invariant forall i ::
         0 <= i < a.Length && !(low <= i < high) ==> a[i] != value
  {
    var mid := (low + high) / 2;
    if a[mid] < value {
      low := mid + 1;
    } else if value < a[mid] {
      high := mid;
    } else {
      return mid;
    }
  }
  return -1;
}

method SelectionSort(a: array<int>)
  modifies a
  ensures multiset(a[..]) == multiset(old(a[..])) // permutation
  ensures forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j] // sorted
{
  var n := a.Length;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant forall k, l :: 0 <= k < l < i ==> a[k] <= a[l]
    invariant forall k, l :: 0 <= k < i <= l < n ==> a[k] <= a[l]
  {
    var minIndex := i;
    var j := i + 1;
    while j < n
      invariant i + 1 <= j <= n
      invariant i <= minIndex < n
      invariant forall k :: i <= k < j ==> a[minIndex] <= a[k]
    {
      if a[j] < a[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    if i != minIndex {
      var tmp := a[i];
      a[i] := a[minIndex];
      a[minIndex] := tmp;
    }
    i := i + 1;
  }
}

method Main()
{
  var input := new int[7];
  input[0], input[1], input[2], input[3], input[4], input[5], input[6] := 10, 4, 7, 2, 8, 3, 1;

  print "Original array: ";
  PrintArray(input);

  SelectionSort(input);

  print "Sorted array: ";
  PrintArray(input);
}

method PrintArray(a: array<int>)
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
  {
    print a[i], " ";
    i := i + 1;
  }
  print "\n";
}
