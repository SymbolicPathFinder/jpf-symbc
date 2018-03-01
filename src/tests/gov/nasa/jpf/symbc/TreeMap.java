/*
 * Copyright (C) 2014, United States Government, as represented by the
 * Administrator of the National Aeronautics and Space Administration.
 * All rights reserved.
 *
 * Symbolic Pathfinder (jpf-symbc) is licensed under the Apache License, 
 * Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 * 
 *        http://www.apache.org/licenses/LICENSE-2.0. 
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and 
 * limitations under the License.
 */
package gov.nasa.jpf.symbc;

import gov.nasa.jpf.vm.Verify;




//import gov.nasa.jpf.extendedtestgen.Debug;

public class TreeMap {

  private transient Entry root = null;

	private transient int size = 0;

	private void incrementSize() { /*modCount++;*/
		size++;
	}

	private void decrementSize() { /*modCount++;*/
		size--;
	}

	public TreeMap() {
	}

	public int size() {
		return size;
	}

	public boolean containsKey(int key) {
		return getEntry(key) != null;
	}

	private Entry getEntry(int key) {
		Entry p = root;
		while (p != null) {
			if (key == p.key) {
				return p;
			} else {
				if (key < p.key) {
					p = p.left;
				} else {
					p = p.right;
				}
			}
		}
		return null;
	}

	public void put(int key) {
		Entry t = root;
		if (t == null) {
			incrementSize();
			root = new Entry(key, null);
			return;
		}
		while (true) {
			if (key == t.key) {
				return;
			} else if (key < t.key) {
				if (t.left != null) {
					t = t.left;
				} else {
					incrementSize();
					t.left = new Entry(key, t);
					fixAfterInsertion(t.left);
					return;
				}
			} else { // key > t.key
				if (t.right != null) {
					t = t.right;
				} else {
					incrementSize();
					t.right = new Entry(key, t);
					fixAfterInsertion(t.right);
					return;
				}
			}
		}
	}

	public void remove(int key) {
		Entry p = getEntry(key);
		if (p == null) {
			return;
		}

		deleteEntry(p);
		return;
	}

	public void print() {
		if (root != null) {
			root.print(0);
		}
	}

	public String toString() {
		String res = "";
		if (root != null) {
			res = root.toString();
		}
		return res;
	}

	public String concreteString(int max_level) {
		String res = "";
		if (root != null) {
			res = root.concreteString(max_level, 0);
		}
		return res;
	}

	private static final boolean RED = false;

	private static final boolean BLACK = true;

	static class Entry {
		int key;

		Entry left = null;

		Entry right = null;

		Entry parent;

		boolean color = BLACK;

		Entry(int key, Entry parent) {
			this.key = key;
			this.parent = parent;
		}

		Entry(int key, Entry left, Entry right, Entry parent, boolean color) {
			this.key = key;
			this.left = left;
			this.right = right;
			this.parent = parent;
			this.color = color;
		}

		public int getKey() {
			return key;
		}

		public String toString() {
			String res = "{ " + (color == BLACK ? "B" : "R") + " ";
			if (left == null) {
				res += "null";
			} else {
				res += left.toString();
			}
			res += " ";
			if (right == null) {
				res += "null";
			} else {
				res += right.toString();
			}
			res += " }";
			return res;
		}

		public String concreteString(int max_level, int cur_level) {
			String res;
			if (cur_level == max_level) {
				res = "{ subtree }";
				//		System.out.println("Brekekek");
			} else {
				res = "{ " + (color == BLACK ? "B" : "R") + key + " ";
				if (left == null) {
					res += "null";
				} else {
					res += left.concreteString(max_level, cur_level + 1);
				}
				res += " ";
				if (right == null) {
					res += "null";
				} else {
					res += right.concreteString(max_level, cur_level + 1);
				}
				res += " }";
			}

			return res;
		}

		public void print(int k) {

			/*for (int i = 0; i < k; i++)
				System.out.print(" ");*/
			//System.out.println(key + (color == BLACK ? "(B)" : "(R)"));

			if (left != null) {
				left.print(k + 2);
			}
			if (right != null) {
				right.print(k + 2);
			}
		}

	}

	private Entry successor(Entry t) {
		if (t == null) {
			return null;
		} else if (t.right != null) {
			Entry p = t.right;
			while (p.left != null) {
				p = p.left;
			}
			return p;
		} else {
			Entry p = t.parent;
			Entry ch = t;
			while (p != null && ch == p.right) {
				ch = p;
				p = p.parent;
			}
			return p;
		}
	}

	private static boolean colorOf(Entry p) {
		return (p == null ? BLACK : p.color);
	}

	private static Entry parentOf(Entry p) {
		return (p == null ? null : p.parent);
	}

	private static void setColor(Entry p, boolean c) {
		if (p != null) {
			p.color = c;
		}
	}

	private static Entry leftOf(Entry p) {
		return (p == null) ? null : p.left;
	}

	private static Entry rightOf(Entry p) {
		return (p == null) ? null : p.right;
	}

	/** From CLR **/
	private void rotateLeft(Entry p) {
		Entry r = p.right;
		p.right = r.left;
		if (r.left != null) {
			r.left.parent = p;
		}
		r.parent = p.parent;
		if (p.parent == null) {
			root = r;
		} else {
			if (p.parent.left == p) {
				p.parent.left = r;
			} else {
				p.parent.right = r;
			}
		}
		r.left = p;
		p.parent = r;
	}

	/** From CLR **/
	private void rotateRight(Entry p) {
		Entry l = p.left;
		p.left = l.right;
		if (l.right != null) {
			l.right.parent = p;
		}
		l.parent = p.parent;
		if (p.parent == null) {
			root = l;
		} else {
			if (p.parent.right == p) {
				p.parent.right = l;
			} else {
				p.parent.left = l;
			}
		}
		l.right = p;
		p.parent = l;
	}

	/** From CLR **/
	private void fixAfterInsertion(Entry x) {
		x.color = RED;
		while (x != null && x != root && x.parent.color == RED) {
			if (parentOf(x) == leftOf(parentOf(parentOf(x)))) {
				Entry y = rightOf(parentOf(parentOf(x)));
				if (colorOf(y) == RED) {
					setColor(parentOf(x), BLACK);
					setColor(y, BLACK);
					setColor(parentOf(parentOf(x)), RED);
					x = parentOf(parentOf(x));
				} else {
					if (x == rightOf(parentOf(x))) {
						x = parentOf(x);
						rotateLeft(x);
					}
					setColor(parentOf(x), BLACK);
					setColor(parentOf(parentOf(x)), RED);
					if (parentOf(parentOf(x)) != null) {
						rotateRight(parentOf(parentOf(x)));
					}
				}
			} else {
				Entry y = leftOf(parentOf(parentOf(x)));
				if (colorOf(y) == RED) {
					setColor(parentOf(x), BLACK);
					setColor(y, BLACK);
					setColor(parentOf(parentOf(x)), RED);
					x = parentOf(parentOf(x));
				} else {
					if (x == leftOf(parentOf(x))) {
						x = parentOf(x);
						rotateRight(x);
					}
					setColor(parentOf(x), BLACK);
					setColor(parentOf(parentOf(x)), RED);
					if (parentOf(parentOf(x)) != null) {
						rotateLeft(parentOf(parentOf(x)));
					}
				}
			}
		}
		root.color = BLACK;
	}

	private void deleteEntry(Entry p) {
		decrementSize();
		// If strictly internal, first swap position with successor.
		if (p.left != null && p.right != null) {
			Entry s = successor(p);
			swapPosition(s, p);
		}
		// Start fixup at replacement node, if it exists.
		Entry replacement = (p.left != null ? p.left : p.right);
		if (replacement != null) {
			replacement.parent = p.parent;
			if (p.parent == null) {
				root = replacement;
			} else {
				if (p == p.parent.left) {
					p.parent.left = replacement;
				} else {
					p.parent.right = replacement;
				}
			}
			p.left = p.right = p.parent = null;
			if (p.color == BLACK) {
				fixAfterDeletion(replacement);
			}
		} else {
			if (p.parent == null) {
				root = null;
			} else {
				if (p.color == BLACK) {
					fixAfterDeletion(p);
				}
				if (p.parent != null) {
					if (p == p.parent.left) {
						p.parent.left = null;
					} else {
						if (p == p.parent.right) {
							p.parent.right = null;
						}
					}
					p.parent = null;
				}
			}
		}
	}

	/** From CLR **/
	private void fixAfterDeletion(Entry x) {
		while (x != root && colorOf(x) == BLACK) {
			if (x == leftOf(parentOf(x))) {
				Entry sib = rightOf(parentOf(x));
				if (colorOf(sib) == RED) {
					//assert false;
					setColor(sib, BLACK);
					setColor(parentOf(x), RED);
					rotateLeft(parentOf(x));
					sib = rightOf(parentOf(x));
				}
				if (colorOf(leftOf(sib)) == BLACK
						&& colorOf(rightOf(sib)) == BLACK) {
					setColor(sib, RED);
					x = parentOf(x);
				} else {
					if (colorOf(rightOf(sib)) == BLACK) {
						setColor(leftOf(sib), BLACK);
						setColor(sib, RED);
						rotateRight(sib);
						sib = rightOf(parentOf(x));
					}
					setColor(sib, colorOf(parentOf(x)));
					setColor(parentOf(x), BLACK);
					setColor(rightOf(sib), BLACK);
					rotateLeft(parentOf(x));
					x = root;
				}
			} else { // symmetric
				Entry sib = leftOf(parentOf(x));
				if (colorOf(sib) == RED) {
					setColor(sib, BLACK);
					setColor(parentOf(x), RED);
					rotateRight(parentOf(x));
					sib = leftOf(parentOf(x));
				}
				if (colorOf(rightOf(sib)) == BLACK
						&& colorOf(leftOf(sib)) == BLACK) {
					setColor(sib, RED);
					x = parentOf(x);
				} else {
					if (colorOf(leftOf(sib)) == BLACK) {
						setColor(rightOf(sib), BLACK);
						setColor(sib, RED);
						rotateLeft(sib);
						sib = leftOf(parentOf(x));
					}
					setColor(sib, colorOf(parentOf(x)));
					setColor(parentOf(x), BLACK);
					setColor(leftOf(sib), BLACK);
					rotateRight(parentOf(x));
					x = root;
				}
			}
		}

		setColor(x, BLACK);
	}

	/**
	 * Swap the linkages of two nodes in a tree.
	 */
	private void swapPosition(Entry x, Entry y) {
		// Save initial values.
		Entry px = x.parent, lx = x.left, rx = x.right;
		Entry py = y.parent, ly = y.left, ry = y.right;
		boolean xWasLeftChild = px != null && x == px.left;
		boolean yWasLeftChild = py != null && y == py.left;
		//	System.out.println("Swap: "+x.key+" "+y.key);
		// Swap, handling special cases of one being the other's parent.
		if (x == py) { // x was y's parent
			x.parent = y;
			if (yWasLeftChild) {
				y.left = x;
				y.right = rx;
			} else {
				y.right = x;
				y.left = lx;
			}
		} else {
			x.parent = py;
			if (py != null) {
				if (yWasLeftChild) {
					py.left = x;
				} else {
					py.right = x;
				}
			}
			y.left = lx;
			y.right = rx;
		}
		if (y == px) { // y was x's parent
			y.parent = x;
			if (xWasLeftChild) {
				x.left = y;
				x.right = ry;
			} else {
				x.right = y;
				x.left = ly;
			}
		} else {
			y.parent = px;
			if (px != null) {
				if (xWasLeftChild) {
					px.left = y;
				} else {
					px.right = y;
				}
			}
			x.left = ly;
			x.right = ry;
		}
		// Fix children's parent pointers
		if (x.left != null) {
			x.left.parent = x;
		}
		if (x.right != null) {
			x.right.parent = x;
		}
		if (y.left != null) {
			y.left.parent = y;
		}
		if (y.right != null) {
			y.right.parent = y;
		}

		// Swap colors
		boolean c = x.color;
		x.color = y.color;
		y.color = c;
		if (root == x) {
			root = y;
		} else {
			if (root == y) {
				root = x;
			}
		}
	}

	public static void main(String[] Argv) {
		TreeMap tree = new TreeMap();

		for (int i=0; i < 3; i++){
			Verify.beginAtomic();
try {
			switch (Verify.random(4)){
			case 0:
				tree.containsKey(0);
				break;
			case 1:
				tree.print();
				break;
			case 2:
				tree.put(i);
				break;
			case 3:
				tree.remove(i);
				break;
			case 4:
				tree.size();
				break;
			}

} catch (Throwable t) {
	// don't care
}

			Verify.endAtomic();
		}



	}
}
