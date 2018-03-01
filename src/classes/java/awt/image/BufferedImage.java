/*
 * Copyright (c) 1997, 2013, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.  Oracle designates this
 * particular file as subject to the "Classpath" exception as provided
 * by Oracle in the LICENSE file that accompanied this code.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */

package java.awt.image;

import gov.nasa.jpf.symbc.Debug;

/**
 *
 * Minimal model for BufferedImage that makes everything symbolic.
 * 
 * @author Rody Kersten
 */

public class BufferedImage // extends java.awt.Image
// implements WritableRenderedImage, Transparency
{
    // Simple model: just int width and height, plus 2-dimensional array of pixels.
    int width;
    int height;
    int pixels[][];

    // each symbolic image has a unique ID
    int id;
    static int nextID = 0;

    // has all these defines
    public static final int TYPE_CUSTOM = 0;
    public static final int TYPE_INT_RGB = 1;
    public static final int TYPE_INT_ARGB = 2;
    public static final int TYPE_INT_ARGB_PRE = 3;
    public static final int TYPE_INT_BGR = 4;
    public static final int TYPE_3BYTE_BGR = 5;
    public static final int TYPE_4BYTE_ABGR = 6;
    public static final int TYPE_4BYTE_ABGR_PRE = 7;
    public static final int TYPE_USHORT_565_RGB = 8;
    public static final int TYPE_USHORT_555_RGB = 9;
    public static final int TYPE_BYTE_GRAY = 10;
    public static final int TYPE_USHORT_GRAY = 11;
    public static final int TYPE_BYTE_BINARY = 12;
    public static final int TYPE_BYTE_INDEXED = 13;

    public BufferedImage(int width, int height, int imageType) {
        this.width = width;
        this.height = height;
        this.pixels = new int[width][height];
        this.id = nextID++;

//        // symbolic pixels
//        for (int x = 0; x < width; x++) {
//            for (int y = 0; y < height; y++) {
//                pixels[x][y] = Debug.makeSymbolicInteger("image" + id + "pixel" + x + ":" + y);
//            }
//        }
    }

    public BufferedImage(int width, int height, int imageType, IndexColorModel cm) {
        this(width, height, imageType);
    }

    public int getType() {
        return TYPE_INT_ARGB;
    }

    public int getRGB(int x, int y) {
        return pixels[x][y];
    }

    public int[] getRGB(int startX, int startY, int w, int h, int[] rgbArray, int offset, int scansize) {
        if (rgbArray == null) {
            rgbArray = new int[w * h];
            offset = 0;
        }

        int i = 0;
        for (int x = startX; x < startX + w; x++) {
            for (int y = startY; y < startY + h; y++) {
                rgbArray[i++] = pixels[x][y];
            }
        }

        return rgbArray;
    }

    public synchronized void setRGB(int x, int y, int rgb) {
        pixels[x][y] = rgb;
    }

    // public void setRGB(int startX, int startY, int w, int h,
    // int[] rgbArray, int offset, int scansize) {
    // //TODO
    // }

    public int getWidth() {
        return width;
    }

    public int getHeight() {
        return height;
    }

    public int getWidth(ImageObserver observer) {
        return width;
    }

    public int getHeight(ImageObserver observer) {
        return height;
    }

    // public BufferedImage getSubimage (int x, int y, int w, int h) {
    // //TODO
    // }

    public String toString() {
        return "Symbolic BufferedImage";
    }

    public int getMinX() {
        return 0;
    }

    public int getMinY() {
        return 0;
    }

    public int getNumXTiles() {
        return 1;
    }

    public int getNumYTiles() {
        return 1;
    }

    public int getMinTileX() {
        return 0;
    }

    public int getMinTileY() {
        return 0;
    }

    public int getTileWidth() {
        return width;
    }

    public int getTileHeight() {
        return height;
    }

    public BufferedImage getCopy() {
        BufferedImage copy = new BufferedImage(width, height, 0);
        for (int x = 0; x < width; x++) {
            for (int y = 0; y < height; y++) {
                copy.setRGB(x, y, pixels[x][y]);
            }
        }
        return copy;
    }

    public ColorModel getColorModel() {
        return null;
    }
}
