class Node<T> {
    var next: Node?<T>
    var data: T

    constructor (data: T)
        ensures this.data == data
        ensures this.next == null;
    {
        this.data := data;
        this.next := null;
    }
}

class Stack<T> {
    var top: Node?<T>

    predicate Valid() 
        reads this
    {
        top == null <==> sizeHelper(top) == 0
    }

    method push(data: T)
        requires Valid()
        modifies this
        ensures fresh(top)
        ensures top.data == data
        ensures top.next == old(top)
        ensures Valid()
    {
        var toAdd := new Node(data);
        toAdd.next := top;
        // top.next := null; // correctly raises a verification error: may update object not in enclosing context's modifies clause
        top := toAdd;
        
        // top := null; // correctly raises a verification error: !fresh(top)
        // top.next := new Node(data); // correctly raises a verification error: top.next != old(top)
    } 

    method peek() returns (data: T)
        requires Valid()
        requires top != null
        ensures data == top.data
        ensures Valid()
    {
        data := top.data;
    }

    method pop() returns (popped: T) 
        requires Valid()
        requires top != null
        modifies this
        ensures top == old(top.next)
        ensures Valid()
    {
        popped := top.data;
        top := top.next;
        
        // top := new Node(popped); // correctly raises a verification error: top != old(top.next)
        // top.data := popped; // correctly raises a verification error: may update object not in enclosing context's modifies clause
        // top.next := null; // correctly raises a verification error: may update object not in enclosing context's modifies clause
    }

    method size() returns (s: int)
        requires Valid()
        ensures s >= 0
        ensures Valid()
    {
        s := sizeHelper(top);
    }

    // unable to prove termination
    function method sizeHelper(node: Node?<T>): int
        ensures sizeHelper(node) >= 0
    {
        if node == null then 0 else 1 + sizeHelper(node.next)
    } 

    method isEmpty() returns (isEmpty: bool) 
        requires Valid()
        ensures top == null <==> isEmpty
        ensures Valid()
    {
        if top == null {
            isEmpty := true;
        } else {
            isEmpty := false;
        }
    }
}

   