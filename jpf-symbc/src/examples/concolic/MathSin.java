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

package concolic;

import gov.nasa.jpf.symbc.Concrete;
import gov.nasa.jpf.symbc.Partition;

/* V4 -- johann 2/2011 */

public class MathSin {

public static final int IEEE_MAX = 2047;
public static final int IEEE_BIAS = 1023;
public static final int IEEE_MANT = 52;

public static final double sixth = 1.0/6.0;
public static final double half = 1.0/2.0;
public static final double mag52 = 1024.*1024.*1024.*1024.*1024.*4.;/*2**52*/
public static final double magic = 1024.*1024.*1024.*1024.*1024.*4.;/*2**52*/

	public static final double[] P = { 
		  -0.64462136749e-9,
		   0.5688203332688e-7,
		  -0.359880911703133e-5,
		   0.16044116846982831e-3,
		  -0.468175413106023168e-2,
		   0.7969262624561800806e-1,
		  -0.64596409750621907082,
		   0.15707963267948963959e1
		 };
	
public static double _2_pi_hi; // = 2.0/Math.PI ;
public static double _2_pi_lo;
public static double pi2_lo;
public static double pi2_hi_hi;
public static double pi2_hi_lo;
public static double pi2_lo_hi;
public static double pi2_lo_lo;
public static double pi2_hi; // = Math.PI/2;
public static double pi2_lo2;

public static final double X_EPS = (double)1e-4;



//========================================================
public double mysin(double x){

		double retval;
		double x_org;
		double x2;

		int md_b_sign;
		int xexp;
		int sign=0;
		int md_b_m1;
		int md_b_m2;
		

	// convert into the different parts
	//
long l_x = Double.doubleToRawLongBits(x);

	//   <32> <20> <11> <1>
	// sign
md_b_sign = (int) ((l_x >> 63) & 1);

	// exponent:  
xexp = (int)((l_x >> 52) & 0x7FF);
int xexp0 = (int)((l_x >> 52) & 0x7FF);

md_b_m2 = (int)(l_x & 0xFFFFFFFF);
md_b_m1 = (int)((l_x >> 31) & 0xFFFFF);
System.out.println("input="+x);
System.out.println("raw="+l_x);
System.out.println("sign="+md_b_sign);
System.out.println("exp="+xexp);
System.out.println("exp_raw="+xexp0);
System.out.println("exp (unbiased)="+(xexp-IEEE_BIAS));
System.out.println("m1="+md_b_m1);
System.out.println("m2="+md_b_m2);

//----------end-of-conversion------------

		if (IEEE_MAX == xexp){
                	System.out.println("NAN-on-INF");
                if( md_b_m1 >0 || md_b_m2 >0  ){
                	System.out.println("unnormalized");
                        retval = x; 
                }else{   
                	System.out.println("NaN");
                	retval = Double.NaN;
                }
		return retval;
		}
		else if (0 == xexp){
			System.out.println("+-0, denormal");
		    	if( md_b_m1>0 || md_b_m2>0 ){	/* denormal	*/
			  System.out.println("denormal");
			  x2 = x*x;	/* raise underflow		*/
			  return x - x2;	/* compute x		*/
			  }
		        else{			/* +/-0.0		*/
			  System.out.println("+-0");
			  return x;	/* => result is argument	*/
		          }
		}
	else if( xexp <= (IEEE_BIAS - IEEE_MANT - 2) ){ /* very small;  */
			System.out.println("very small");
			return x;
		 }else if( xexp <= (IEEE_BIAS - IEEE_MANT/4) ){ /* small */
			 System.out.println("small");
             		return x*(1.0-x*x*sixth); 
				/* x**4 < epsilon of x        */
             		}
	

		if (md_b_sign == 1){
			x = -x;
			sign = 1;
			}
		x_org = x;


System.out.println("CURRENT\n\n");


		if (xexp < IEEE_BIAS){
			System.out.println("less-than pi/2");
			;
		}else if (xexp <= (IEEE_BIAS + IEEE_MANT)){
			System.out.println("must bring into range...");
			double xm; 
			double x3 =0.0;
			double x4 =0.0;
			double x5 =0.0;
			double x6 =0.0;
			double a1=0.0;
			double a2=0.0;
            		int bot2;  
            		double xn_d;
            		double md; // should be bit union
            
            xm = Math.floor(x * _2_pi_hi + half);
		System.out.println("xm (int) = " + xm);
            xn_d = xm + mag52;

	    System.out.println("xn_d = " + xn_d);
	    // C: bot2 = xn.b.m2 & 3u;
            // bot2 is the lower 3 bits of M2
            long l_xn = Double.doubleToRawLongBits(xn_d);

            int xn_m2 = (int)(l_xn & 0xFFFFFFFF);
            bot2 = xn_m2 & 3;
	    System.out.println("bot2 = " + bot2);
            

                /*
                 * Form xm * (pi/2) exactly by doing:
                 *      (x3,x4) = xm * pi2_hi
                 *      (x5,x6) = xm * pi2_lo
                 */
//>>>>>>>>>>>>>>>>>>>>>                split(a1,a2,xm);
System.out.println("splitting: "+xm);
long l_x1 = Double.doubleToRawLongBits(xm);

	//   <32> <20> <11> <1>
	// sign
int md_b_sign1 = (int) ((l_x1 >> 63) & 1);
	// exponent:  
int xexp1 = (int)((l_x1 >> 52) & 0x7FF);
int md_b_m21 = (int)(l_x1 & 0xFFFFFFFF);
int md_b_m11 = (int)((l_x1 >> 31) & 0xFFFFF);
System.out.println("raw="+l_x1);
System.out.println("sign="+md_b_sign1);
System.out.println("exp="+xexp1);
System.out.println("exp (unbiased)="+(xexp1-IEEE_BIAS));
System.out.println("m1="+md_b_m11);
System.out.println("m2="+md_b_m21);

// 	md.b.m2 &= 0xfc000000u;		\
// md_b_m2 = (int)(l_x1 & 0xFFFFFFFF);
l_x1 &= (long)0xFC000000L;		
a1 = Double.longBitsToDouble(l_x1);
// 	lo = (v) - hi;	/* bot 26 bits */
a2 = xm - a1;

System.out.println("in split: a1="+a1);
System.out.println("in split: a2="+a2);

//>>>>>>>>>>> exactmul2(x3,x4, xm,a1,a2, pi2_hi,pi2_hi_hi,pi2_hi_lo);
	x3 = (xm)*(pi2_hi); 
	x4 = (((a1*pi2_hi_hi-x3)+a1*pi2_hi_lo)+pi2_hi_hi*a2)+a2*pi2_hi_lo;;

//>>>>>>>>>>>  exactmul2(x5,x6, xm,a1,a2, pi2_lo,pi2_lo_hi,pi2_lo_lo);
        x5 = (xm)*(pi2_lo); 
	x6 = (((a1*pi2_lo_hi-x5)+a1*pi2_lo_lo)+pi2_lo_hi*a2)+a2*pi2_lo_lo;;

                x = ((((x - x3) - x4) - x5) - x6) - xm*pi2_lo2;


	    //++++++++++++++++++++++++++++++++++++++++++++++
            
            switch(bot2){
            case 0:
                    if (x < 0.0) {
                            x = -x;
                            //sign ^= 1;
                            if (sign ==1)
                            		sign = 0;
                            else
                            		sign = 1;
                    }
                    break;
            case 1:
                    if( x < 0.0 ){
                            x = pi2_hi + x;
                    }else{
                            x = pi2_hi - x;
                    }
                    break;
            case 2:
                    if (x < 0.0) {
                            x = -x;
                    }else{
                     
                          //sign ^= 1;
                            if (sign ==1)
                            		sign = 0;
                            else
                            		sign = 1;
                    }
                    break;
            case 3:
                    // sign ^= 1;
                    if (sign ==1)
                		sign = 0;
                    else
                		sign = 1;
                    
                    if( x < 0.0 ){
                            x = pi2_hi + x;
                    }else{
                            x = pi2_hi - x;
                    }
                    break;
            default:;
            }
		}else {
			System.out.println("T_LOSS ");
			retval = 0.0;
			if (sign == 1)
				retval = -retval;
			return retval;
		}

//---------everything between 0..pi/2
		
		x = x * _2_pi_hi;
		
		 
        if (x > X_EPS){
		System.out.println("x > EPS");
                x2 = x*x;
                x *= ((((((((P)[0]*(x2) + (P)[1])*(x2) + 
                	(P)[2])*(x2) + (P)[3])*(x2) + (P)[4])*(x2) + 
			(P)[5])*(x2) + (P)[6])*(x2) + (P)[7]);
        }else {
		System.out.println("x <= EPS");
        	x *= pi2_hi;              /* x = x * (pi/2)               */
		}

        if (sign==1) x = -x;
        System.out.println("final return");
        return x;
		}

//===============AUX========================
public MathSin(){

//#define MD(v,hi,lo) md.i.i1 = hi; md.i.i2 = lo; v = md.d;

//	  MD(    pi_hi, 0x400921FBuL,0x54442D18uL);/* top 53 bits of PI	*/
// pi_hi = Double.longBitsToDouble((long)0x400921FB54442D18L);
// System.out.println("pi_hi = " + pi_hi);
//	  MD(    pi_lo, 0x3CA1A626uL,0x33145C07uL);/* next 53 bits of PI*/
// pi_lo = Double.longBitsToDouble((long)0x3CA1A62633145C07L);
// System.out.println("pi_lo = " + pi_lo);

//	  MD(   pi2_hi, 0x3FF921FBuL,0x54442D18uL);/* top 53 bits of PI/2 */
pi2_hi = Double.longBitsToDouble((long)0x3FF921FB54442D18L);
System.out.println("pi2_hi = " + pi2_hi);
//	  MD(   pi2_lo, 0x3C91A626uL,0x33145C07uL);/* next 53 bits of PI/2*/
pi2_lo = Double.longBitsToDouble((long)0x3C91A62633145C07L);
System.out.println("pi2_lo = " + pi2_lo);


//	  MD(  pi2_lo2, 0xB91F1976uL,0xB7ED8FBCuL);/* next 53 bits of PI/2*/
pi2_lo2 = Double.longBitsToDouble((long)0xB91F1976B7ED8FBCL);
System.out.println("pi2_lo2 = " + pi2_lo2);

//	  MD( _2_pi_hi, 0x3FE45F30uL,0x6DC9C883uL);/* top 53 bits of 2/pi */
_2_pi_hi = Double.longBitsToDouble((long)0x3FE45F306DC9C883L);
System.out.println("_2_pi_hi = " + _2_pi_hi);
//	  MD( _2_pi_lo, 0xBC86B01EuL,0xC5417056uL);/* next 53 bits of 2/pi*/
_2_pi_lo = Double.longBitsToDouble((long)0xBC86B01EC5417056L);
System.out.println("_2_pi_lo = " + _2_pi_lo);



//>>>>>	  split(pi2_hi_hi,pi2_hi_lo,pi2_hi);
double a1,a2;
double xm;
xm=pi2_hi;
System.out.println("splitting: "+xm);
long l_x1 = Double.doubleToRawLongBits(xm);

	//   <32> <20> <11> <1>
	// sign
int md_b_sign1 = (int) ((l_x1 >> 63) & 1);
	// exponent:  
int xexp1 = (int)((l_x1 >> 52) & 0x7FF);
int md_b_m21 = (int)(l_x1 & 0xFFFFFFFF);
int md_b_m11 = (int)((l_x1 >> 31) & 0xFFFFF);
System.out.println("raw="+l_x1);
System.out.println("sign="+md_b_sign1);
System.out.println("exp="+xexp1);
System.out.println("exp (unbiased)="+(xexp1-IEEE_BIAS));
System.out.println("m1="+md_b_m11);
System.out.println("m2="+md_b_m21);

// 	md.b.m2 &= 0xfc000000u;		\
// md_b_m2 = (int)(l_x1 & 0xFFFFFFFF);
l_x1 &= (long)0xFC000000L;		
a1 = Double.longBitsToDouble(l_x1);
// 	lo = (v) - hi;	/* bot 26 bits */
a2 = xm - a1;

System.out.println("in split: a1="+a1);
System.out.println("in split: a2="+a2);
pi2_hi_hi=a1;
pi2_hi_lo=a2;


//>>>>>	  split(pi2_lo_hi,pi2_lo_lo,pi2_lo);
xm=pi2_lo;
System.out.println("splitting: "+xm);
//l_x1 = Double.doubleToRawLongBits(xm);
l_x1 = MathSin.helperdoubleToRawBits(xm);
	//   <32> <20> <11> <1>
	// sign
md_b_sign1 = (int) ((l_x1 >> 63) & 1);
	// exponent:  
xexp1 = (int)((l_x1 >> 52) & 0x7FF);
md_b_m21 = (int)(l_x1 & 0xFFFFFFFF);
md_b_m11 = (int)((l_x1 >> 31) & 0xFFFFF);
System.out.println("raw="+l_x1);
System.out.println("sign="+md_b_sign1);
System.out.println("exp="+xexp1);
System.out.println("exp (unbiased)="+(xexp1-IEEE_BIAS));
System.out.println("m1="+md_b_m11);
System.out.println("m2="+md_b_m21);

// 	md.b.m2 &= 0xfc000000u;		\
// md_b_m2 = (int)(l_x1 & 0xFFFFFFFF);
l_x1 &= (long)0xFC000000L;		
a1 = Double.longBitsToDouble(l_x1);
// 	lo = (v) - hi;	/* bot 26 bits */
a2 = xm - a1;

System.out.println("in split: a1="+a1);
System.out.println("in split: a2="+a2);

pi2_lo_hi=a1;
pi2_lo_lo=a2;

}

@Concrete("true")
public static long helperdoubleToRawBits(double xm) {
	return Double.doubleToRawLongBits(xm);
}



//====================================================
public void TESTIT(double arg){

	
	
double ms = mysin(arg);
System.out.println("SIN("+arg+"):\t"+Math.sin(arg) +"\tmysin: "+ms);
}
	/**
	 * @param args
	 */
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		MathSin sin = new MathSin();
		if(sin.mysin(0.0) == 0.0) {
			System.out.println("it is zero");
		}
sin.TESTIT((double)0);
sin.TESTIT((double)-0);
sin.TESTIT((double)1e-200);
sin.TESTIT((double)1e-100);
sin.TESTIT((double)1e-10);
sin.TESTIT((double)1e-5);
sin.TESTIT((double)0.001);
sin.TESTIT((double)0.5);
sin.TESTIT((double)0.8);
sin.TESTIT((double)1);
sin.TESTIT((double)5);
sin.TESTIT((double)20);
sin.TESTIT((double)1e99);
sin.TESTIT((double)-1e-200);
sin.TESTIT((double)-1e-100);
sin.TESTIT((double)-1e-10);
sin.TESTIT((double)-1e-5);
sin.TESTIT((double)-0.001);
sin.TESTIT((double)-0.5);
sin.TESTIT((double)-0.8);
sin.TESTIT((double)-1);
sin.TESTIT((double)-5);
sin.TESTIT((double)-20);
sin.TESTIT((double)-1e99);
	}
}


	/**
	 * @param args
	 */
/*	public static void main(String[] args) {
		// TODO Auto-generated method stub
	   // MathSin.calc(1.0);
		double x = 0.0;
		while(x < 100) {
			System.out.println("calculate "+x + "..." +MathSin.calculate(x));
			x = x+ 0.5;
		}

	  //  double x = MathSin.calculate(0.0);
     //  System.out.println("0 -->" + x);
     //  System.out.println("1e-55 --> "+ MathSin.calculate(1e-55)); //1.0E-55
     //  System.out.println("1e-1 -->"+ MathSin.calculate(1e-1)); // 0.0
     //  System.out.println("1 -->"+ MathSin.calculate(1.0)); // 0.0
    //   System.out.println("0.12 -->" + MathSin.calculate(1.2));
      //  Debug.printPC("\nMathSin.calculate Path Condition: ");

	}

	public static void calc(double x) {
		 if(MathSin.calculate(x) == 0) {
		    	System.out.println("value of 0.0 ----- br1 !!!!!!!!!!!!!!!!!!!");
		 }
		  if(MathSin.calculate(x) == 1.0E-55) {
		    	System.out.println("\n value of 1e-55 ----- br2 !!!!!!!!!!!!!!!!!!");
		 }
	}
}

*/