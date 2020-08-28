class Node<T> {
    var next: Node?<T>
    var data: T

    constructor (data: T)
        ensures this.data == data
    {
        this.data := data;
    }
}

class Stack<T> {
    var top: Node?<T>

    method push(data: T)
        modifies this
        ensures top != null
        ensures top.data == data
        ensures top.next == old(top)
    {
        var toAdd := new Node(data);
        toAdd.next := top;
        // top.next := null; // correctly raises a verification error: may update object not in enclosing context's modifies clause
        top := toAdd;
        // top.next := new Node(data); // correctly raises a verification error: top.next != old(top)
    } 

    method peek() returns (data: T)
        requires top != null
        ensures data == top.data
    {
        data := top.data;
    }

    method pop() returns (popped: T) 
        requires top != null
        modifies this
        ensures top == old(top.next)
    {
        popped := top.data;
        top := top.next;
        
        // top := new Node(popped); // correctly raises a verification error: top != old(top.next)
        // top.data := popped; // correctly raises a verification error: may update object not in enclosing context's modifies clause
        // top.next := null; // correctly raises a verification error: may update object not in enclosing context's modifies clause
    }

    method isEmpty() returns (isEmpty: bool) 
        ensures top == null ==> isEmpty
        ensures top != null ==> !isEmpty
    {
        if top == null {
            isEmpty := true;
        } else {
            isEmpty := false;
        }
    }
}

   