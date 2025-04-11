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

/**
 * This class tests the behaviour of {@code Math.max()} and {@code Math.min()} methods.
 * <p>
 *     Edge case handling of {@code NaN} and {@code 0.0/-0.0}
 * </p>
 */

public class TestMathMaxMin {

    /**
     * This method tests {@code Math.max()} for {@code double} type values.
     */

    public static void testDoubleMax() {

        /* This will pass as exact bit representations of 0.0 and -0.0 are not equal.
           But earlier If we kept -0.0 as the first argument it was returning -0.0, which is wrong. */
        assert Double.doubleToRawLongBits(Math.max(-0.0, 0.0)) == Double.doubleToRawLongBits(0.0) : "Test case Failed";

        // This will fail
        assert Double.doubleToRawLongBits(Math.max(0.0, -0.0)) == Double.doubleToRawLongBits(-0.0) : "Test case Failed as Expected";

        /* This will fail as expected which is the right behaviour, earlier Math.max() returned 5.0
           Similar to the case above. */
        assert Double.doubleToRawLongBits(Math.max(Double.NaN, 5.0)) == Double.doubleToRawLongBits(5.0) : "Test case Failed as Expected";

        // Eventually this will pass now
        assert Double.doubleToRawLongBits(Math.max(5.0, Double.NaN)) == Double.doubleToRawLongBits(Double.NaN) : "Test case Failed";

        // Additional Tests, similar to the cases above.
        assert Double.doubleToRawLongBits(Math.max(Double.NaN, Double.POSITIVE_INFINITY)) == Double.doubleToRawLongBits(Double.NaN) : "Test case Failed"; // earlier this returned +Infinity, but should be NaN
        assert Double.doubleToRawLongBits(Math.max(Double.NaN, Double.NEGATIVE_INFINITY)) == Double.doubleToRawLongBits(Double.NaN) : "Test case Failed"; // earlier this returned -Infinity, but should be NaN

    }


    /**
     * This method tests {@code Math.max()} for {@code float} type values.
     */

    public static void testFloatMax() {

        // Tests similar to the cases above.
        assert Math.max(0.0f, -0.0f) == 0.0 : "Test case Failed"; // 0.0

        assert Float.floatToRawIntBits(Math.max(-0.0f, 0.0f)) == Float.floatToRawIntBits(0.0f) : "Test case Failed"; // 0.0

        assert Float.floatToRawIntBits(Math.max(Float.NaN, 4.5f)) == Float.floatToRawIntBits(Float.NaN) : "Test case Failed"; // NaN

        assert Float.floatToRawIntBits(Math.max(Float.NaN, Float.POSITIVE_INFINITY)) == Float.floatToRawIntBits(Float.NaN) : "Test case Failed"; // NaN
    }


    /**
     * This method tests {@code Math.min()} for {@code double} type values.
     */

    public static void testDoubleMin() {

         /* Earlier this was returning 0.0, -0.0, 4.5, 9.0 and -Infinity
            min => should be a <= b not a >= b */
        assert Double.doubleToRawLongBits(Math.min(0.0, -0.0)) == Double.doubleToRawLongBits(-0.0) : "Test case Failed"; // -0.0

        assert Double.doubleToRawLongBits(Math.min(-0.0, 0.0)) == Double.doubleToRawLongBits(-0.0) : "Test case Failed"; // -0.0

        assert Double.doubleToRawLongBits(Math.min(Double.NaN, 4.5)) == Double.doubleToRawLongBits(Double.NaN) : "Test case Failed"; // NaN

        assert Math.min(5.0, 9.0) == 5.0 : "Test case Failed"; // 5.0

        //Additional Test case
        assert Double.doubleToRawLongBits(Math.min(Double.NaN, Double.NEGATIVE_INFINITY)) == Double.doubleToRawLongBits(Double.NaN) : "Test case Failed"; // NaN
    }


    /**
     * This method tests {@code Math.min()} for {@code double} type values.
     */

    public static void testFloatMin() {

        // Tests similar to the cases above.
        assert Float.floatToRawIntBits(Math.min(0.0f, -0.0f)) == Float.floatToRawIntBits(-0.0f) : "Test case Failed"; // -0.0

        assert Float.floatToRawIntBits(Math.min(Float.NaN, 4.5f)) == Float.floatToRawIntBits(Float.NaN) : "Test case Failed"; // NaN

        assert Float.floatToRawIntBits(Math.min(Float.POSITIVE_INFINITY, Float.NEGATIVE_INFINITY)) == Float.floatToRawIntBits(Float.NEGATIVE_INFINITY) : "Test case Failed"; // -Infinity
    }

    public static void main(String[] args) {

        testDoubleMax(); // Math.max() for double type values.
        testFloatMax(); // Math.max() for float type values.

        testDoubleMin(); // Math.min() for double type values
        testFloatMin(); // Math.min()  for float type values
    }
}

