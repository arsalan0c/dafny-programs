class Node<T> {
    var next: Node?<T>
    var data: T

    constructor (data: T)
        ensures this.data == data
        ensures this.next == null
    {
        this.data := data;
        this.next := null;
    }
}

class Queue<T> {
    var first: Node?<T>
    var last: Node?<T>

    predicate Valid()
        reads this
        reads last
    {   
        first == null <==> last == null &&
            last != null ==> last.next == null
    }

    method enqueue(data: T)
        requires Valid()
        modifies this
        modifies first
        modifies last
        ensures fresh(last)
        ensures first == null ==> fresh(first) // why does iff fail to satisfy this?
        ensures Valid() // why does this fail?
    {
        var toEnqueue := new Node(data);
        if (last != null) {
            last.next := toEnqueue;
        } 
        last := toEnqueue;
        if (first == null) {
            first := toEnqueue;
        }
    }

    method dequeue(data: T) returns (dequeued: T)
        requires Valid()
        requires first != null
        modifies this
        ensures first == old(first.next)
        ensures Valid()
    {
        dequeued := first.data;
        first := first.next;
        if first == null {
            last := null;
        }
    }

    method peek() returns (data: T) 
        requires Valid()
        requires first != null
        ensures data == first.data
        ensures Valid()
    {
        data := first.data;
    }

    method isEmpty() returns (isEmpty: bool) 
        requires Valid()
        ensures first == null <==> isEmpty
        ensures Valid()
    {
        if (first == null) {
            isEmpty := true;
        } else {
            isEmpty := false;
        }
    }
}