/*
 * Copyright (C)  2022  Franck van Breugel
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

/**
 * A simple example.
 * 
 * @author Franck van Breugel
 */
public class Example {

	/**
	 * Returns the minimum of the given integers. 
	 * 
	 * @param x an integer
	 * @param y an integer
	 * @return the minimum of x and y
	 */
	private static int min(int x, int y) {
		if (x > y) {
			// swap x and y
			x = x + y;
			y = x - y;
			x = x - y;
		}
		if (x > y) {
			assert false;
		}
		return x;
	}
	
	public static void main(String[] args) {
		Example.min(0, 1);
	}
}
