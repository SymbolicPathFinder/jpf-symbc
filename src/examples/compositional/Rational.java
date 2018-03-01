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

package compositional;
// when we win
// 1. simplify the constraints in the summary: we should do it
// 2. we only do one check


import gov.nasa.jpf.vm.Verify;
import gov.nasa.jpf.symbc.Preconditions;

public class Rational{

    private int num;
    private int den;
    
    public Rational(){
        num = 0;
        den = 1;
    }

    public Rational(int n,int d){
        num = n;
        den = d;
    }

    public static int abs(int x){
	if (x >= 0) return x;
	else return -x;
    }

    @Preconditions("x>=0")
    public static int abs_summary_case1(int x){
    		return x;
    }
    
    @Preconditions("x<0")
    public static int abs_summary_case2(int x){
    		return -x;
    }
    
    public static int abs_summary(int x){
    	int tmpa=0;
    	if(Verify.randomBool()){
	    	// summary case 1: check precondition    
    		if(x>=0)
    			tmpa=abs_summary_case1(x);
    		else
        		Verify.ignoreIf(true);	
	    }
	    else {
	    	// summary case 2
	    	if(x<0)
	    		tmpa=abs_summary_case2(x);
	    	else
        		Verify.ignoreIf(true);	
	    }
    	return tmpa;
    }
    public static int gcd(int a,int b){
	/*
    	int res;
		while (b != 0){
	    	res = a%b;
	    	a = b;
	    	b = res;
	   
		}
		return abs(a);
		*/
    	int c = abs(a);
    	if (c == 0)
    		return abs(b);
    	
    	int count=0;
    	while (b != 0) {
    		count++;
    		System.out.println("count "+count);
    		if(count>=4) assert false;
    		if (c > b)
    			c = c-b;
    		else
    			b = b-c;
    	}
    	return c;
    }	

    /* Precondition:
     * (b_2_SYMINT[100] - (CONST_0 - a_1_SYMINT[-100])) == CONST_0 &&
		(CONST_0 - a_1_SYMINT[-100]) <= b_2_SYMINT[100] &&
		b_2_SYMINT[100] != CONST_0 &&
		(CONST_0 - a_1_SYMINT[-100]) != CONST_0 &&
		a_1_SYMINT[-100] < CONST_0
		Return is:  (CONST_0 - a_1_SYMINT[-100])
    */
    public static int gcd_composition_summary_case1(int a,int b){
    	if(b+a==0 && -a <=b && b!=0 && -a !=0 && a<0) {
    		//return -a;
    		int c = abs_summary(a);
        	int count=0;
        	count++;
        	b = b-c;
        	return c;
    	}
    	else
    		Verify.ignoreIf(true);
    	return 0;
    }
    /* Precondition: 
     * PC is:constraint # = 3
		b_2_SYMINT[0] == CONST_0 &&
		(CONST_0 - a_1_SYMINT[-88]) != CONST_0 &&
		a_1_SYMINT[-88] < CONST_0
		Return is:  (CONST_0 - a_1_SYMINT[-88])
     */
    public static int gcd_composition_summary_case2(int a,int b){
    	if(b==0 && -a!=0 && a<0) {
    		//return -a;
    		int c = abs_summary(a);
        	int count=0;
        	return c;
    	}
    	else
    		Verify.ignoreIf(true);
    	return 0;
    }
    /* Precondition:
     * PC is:constraint # = 3
	b_2_SYMINT[-88] < CONST_0 &&
	a_1_SYMINT[0] == CONST_0 &&
	a_1_SYMINT[0] >= CONST_0
	Return is:  (CONST_0 - b_2_SYMINT[-88])
     */
    public static int gcd_composition_summary_case3(int a,int b){
    	if(b<0 && a==0 && a>=0) {
    		//return -b;
    		int c = abs_summary(a);
        	b=abs_summary(b);
        	return b;
    	}
    	else
    		Verify.ignoreIf(true);
    	return 0;
    }
    /* Precondition:
     * PC is:constraint # = 3
		b_2_SYMINT[0] >= CONST_0 &&
		a_1_SYMINT[0] == CONST_0 &&
		a_1_SYMINT[0] >= CONST_0
		Return is:  b_2_SYMINT[0]
     */
    public static int gcd_composition_summary_case4(int a,int b){
    	if(b>=0 && a==0 && a>=0) {
    		//return b;
    		int c = abs_summary(a);
        	b=abs_summary(b);
        	return b;
    	}
    	else
    		Verify.ignoreIf(true);
    	return 0;
    }
    
    public static int gcd_composition(int a,int b){
    	    int c = abs_summary(a);
        	if (c == 0) {
        		b=abs_summary(b);
        		return b;
        	}
        	int count=0;
        	while (b != 0) {
        		count++;
        		if(count>=2) assert false;
        		if (c > b)
        			c = c-b;
        		else
        			b = b-c;
        	}
        	return c;
        }	
    
    
    public void simplify(){
        int gcd = gcd(num,den);	
        num = num/gcd;
        den = den/gcd;
    }

    public static Rational[] simp(Rational[] rs){
        int length = rs.length;
        Rational[] oldRs = new Rational[length];
        arraycopy(rs,oldRs,length);
        for (int i = 0;i < length;i++)
            rs[i].simplify();
        return oldRs;
    }

    public boolean equals(Object obj){
	if (obj instanceof Rational){
                Rational rat= (Rational) obj;
                return this.num==rat.num && this.den==rat.den;
             }
        return false;
    }
    
    public float toFloat(){
	return ((float) num/den);
    }
    
    public String toString(){
	if (den != 1)
	    return num + "/" + den;
	else
	    return String.valueOf(num);
    }
    
    public Rational mul(Rational r){
	return new Rational(num * r.num,den * r.den);
    }

    public Rational div(Rational r){
	return new Rational(num * r.den,den * r.num);
    }
    
    public static void arraycopy(Object[] src,Object[] dest,int length){
	if (length < 0) throw new ArithmeticException();//ArrayIndexOutOfBoundsException();
	for (int i = 0; i < length; i++)
	    dest[i] = src[i];
    }
        
    private static void printArray(Rational[] rs){
	for (int i = 0;i < rs.length;i++)
	    System.out.print(rs[i].toString() + " ");
	System.out.println();
    }
    
    public static void test(int i1, int i2, int i3, int i4, int i5, int i6) {
    	    Rational r0 = new Rational(i1,i2);
    		Rational r1 = new Rational(i3,i4);
    		Rational r2 = new Rational(i5,i6);
    		Rational[] rs = new Rational[3];
    		rs[0] = r0; rs[1] = r1; rs[2] = r2;
    		//System.out.print("Original array: ");
    		//printArray(rs);
    		Rational[] oldRs = simp(rs);
    		//System.out.print("Simplified array: ");
    		//printArray(rs);
    		//System.out.print("Copied array: ");
    		//printArray(oldRs);
    }
    public static void main(String[] args){
	/*
    Rational r0 = new Rational(5,10);
	Rational r1 = new Rational(2,10);
	Rational r2 = new Rational(4,6);
	Rational[] rs = new Rational[3];
	rs[0] = r0; rs[1] = r1; rs[2] = r2;
	System.out.print("Original array: ");
	printArray(rs);
	Rational[] oldRs = simp(rs);
	System.out.print("Simplified array: ");
	printArray(rs);
	System.out.print("Copied array: ");
	printArray(oldRs);
	*/
    	//test(5,10,2,10,4,6);
    	//abs(0);
    	gcd_composition(0,0);
    	
    }

}
