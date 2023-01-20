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

package gov.nasa.jpf.symbc.strings;

public class MysteryQuestion {
	
	public static void main (String[] args) {
		preserveSomeHtmlTagsAndRemoveWhitespaces("b");
	}

	private static String stripTags( String s )
    {
        // null is still null
        if( s == null ) {
            return null;
        }
        // find potential start of first tag
        int i = s.indexOf('<');
        if( i < 0 ) {
            // no tags encountered
            return s;
        }
        // prepare result buffer
        int len = s.length();
        StringBuffer sb = new StringBuffer( len );
        int current=0;
        while( i >= 0 ) {
            // strip everything inside <script> tags
            if (len >= i+ 7 && s.substring(i, i+7).equalsIgnoreCase("<script")) {
                int j = s.indexOf("</script>", i);
                if (j == -1) j = s.indexOf("</SCRIPT>", i);
                if (j > 0) {
                    sb.append(s.substring(current, i));
                    current = j + 9;
                    i = s.indexOf('<', current);
                    continue;
                }
            }
            // strip everything inside <style> tags
            if (len >= i+ 6 && s.substring(i, i+6).equalsIgnoreCase("<style")) {
                int j = s.indexOf("</style>", i);
                if (j == -1) j = s.indexOf("</STYLE>", i);
                if (j > 0) {
                    sb.append(s.substring(current, i));
                    current = j + 8;
                    i = s.indexOf('<', current);
                    continue;
                }
            }
            // find potential end of tag
            int j = s.indexOf('>',i);
            if( j < 0 ) {
                // no more end of tags found - done
                // append the rest of the string
                sb.append(s.substring(current));
                current = len;
                break;
            }
            else {
                // end of tag found
                sb.append(s.substring(current,i));
                current=j+1;
                i = s.indexOf('<',current);
            }
        }
        if( current < s.length() ) {
            // add in remainder, if any
            sb.append(s.substring(current));
        }
        return sb.toString();
    }
	
	public static String preserveSomeHtmlTagsAndRemoveWhitespaces(String body) {
		if (body == null)
			return body;
		int i = 0;
		StringBuffer sb = new StringBuffer(body.length());
		boolean withInPreformat = false;
		int len = body.length();
		while (i < len) {
			char c = body.charAt(i);
			try {
				if (c == '<') {
					if (i + 14 < len &&
					(body.charAt(i + 8) == '\"')
					&&
					(body.charAt(i + 7) == '=')
					&&
					(body.charAt(i + 6) == 'f' || body.charAt(i + 6) == 'F')
					&&
					(body.charAt(i + 5) == 'e' || body.charAt(i + 5) == 'E')
					&&
					(body.charAt(i + 4) == 'r' || body.charAt(i + 4) == 'R')
					&&
					(body.charAt(i + 3) == 'h' || body.charAt(i + 3) == 'H')
					&&
					(body.charAt(i + 2) == ' ')
					&&
					(body.charAt(i + 1) == 'a' || body.charAt(i + 1) == 'A')
					) {
						String href = "";
						String dispText = "";
						int idx = i + 9;
						int idx2 = body.indexOf("\"", idx);
						if (idx2 > 0) {
							href = body.substring(idx, idx2); //storing actual link in href
						}
						int idxStart = body.indexOf('>', idx2);
						int idxEnd = body.indexOf("</a>", idxStart);
						if (idxEnd == -1)
							idxEnd = body.indexOf("</A>", idxStart);
						if ((idxStart > 0) && (idxEnd > idxStart + 1)) {
							dispText = body.substring(idxStart + 1, idxEnd);
							dispText = stripTags(dispText);
							dispText = dispText.trim();
						}
						if (!"".equals(href) && !"".equals(href)) {
							if (href.startsWith("mailto:")
									|| href.startsWith("MAILTO:")) { //if an email link removing mailto:
								href = href.substring(7);
							}
							if (dispText.equals(href)) {
								sb.append(dispText);
							}
							else {
								sb.append(dispText + " [  " + href + "  ] ");
							}
						} else {
							sb.append(dispText);
						}
						i = idxEnd + 4;
						continue;
					}

					if (i + 4 < len &&
					(body.charAt(i + 4) == '>')
					&&
					(body.charAt(i + 3) == 'e' || body.charAt(i + 3) == 'E')
					&&
					(body.charAt(i + 2) == 'r' || body.charAt(i + 2) == 'R')
					&&
					(body.charAt(i + 1) == 'p' || body.charAt(i + 1) == 'P')
					) {
						withInPreformat = true;
						i += 5;
						continue;
					}
					if (i + 5 < len &&
					(body.charAt(i + 5) == '>')
					&&
					(body.charAt(i + 4) == 'e' || body.charAt(i + 4) == 'E')
					&&
					(body.charAt(i + 3) == 'r' || body.charAt(i + 3) == 'R')
					&&
					(body.charAt(i + 2) == 'p' || body.charAt(i + 2) == 'P')
					&&
					(body.charAt(i + 1) == '/')
					) {
						withInPreformat = false;
						i += 6;
						continue;
					}
					char last_appended_char = '\n';
					int sblen = sb.length();
					if (sblen > 0) {
						last_appended_char = sb.charAt(sblen - 1);
					}
					// do <br>
					if (
					(i + 3 < len)
					&&
					(body.charAt(i + 3) == '>')
					&&
					(body.charAt(i + 2) == 'r' || body.charAt(i + 2) == 'R')
					&&
					(body.charAt(i + 1) == 'b' || body.charAt(i + 1) == 'B')
					) {
						sb.append("\n");
						i = i + 4;
					}
					if ( //do <br />
					(i + 5 < len)
					&&
					(body.charAt(i + 5) == '>')
					&&
					(body.charAt(i + 4) == '/')
					&&
					(body.charAt(i + 3) == ' ')
					&&
					(body.charAt(i + 2) == 'r' || body.charAt(i + 2) == 'R')
					&&
					(body.charAt(i + 1) == 'b' || body.charAt(i + 1) == 'B')
					) {
						sb.append("\n");
						i = i + 6;
					} else if (
					(i + 2 < len)
					&&
					(body.charAt(i + 2) == '>')
					&&
					(body.charAt(i + 1) == 'p' || body.charAt(i + 1) == 'P')
					) {
						if (last_appended_char != '\n'
								&& last_appended_char != '\r') {
							//only append it if it's not on it's own line already
							sb.append("\n\n");
						}
						i = i + 3;
					} else if (
					(i + 3 < len)
					&&
					(body.charAt(i + 3) == '>')
					&&
					(body.charAt(i + 2) == 'p' || body.charAt(i + 2) == 'P')
					&&
					(body.charAt(i + 1) == '/')
					) {
						sb.append("\n\n");
						i = i + 4;
					} else if (
					(i + 4 < len)
					&&
					(body.charAt(i + 4) == '>')
					&&
					(body.charAt(i + 3) == 'v' || body.charAt(i + 3) == 'V')
					&&
					(body.charAt(i + 2) == 'i' || body.charAt(i + 2) == 'I')
					&&
					(body.charAt(i + 1) == 'd' || body.charAt(i + 1) == 'D')
					) {
						if (last_appended_char != '\n'
								&& last_appended_char != '\r') {
							sb.append("\n");
						}
						i = i + 5;
					} else if (
					(i + 5 < len)
					&&
					(body.charAt(i + 5) == '>')
					&&
					(body.charAt(i + 4) == 'v' || body.charAt(i + 4) == 'V')
					&&
					(body.charAt(i + 3) == 'i' || body.charAt(i + 3) == 'I')
					&&
					(body.charAt(i + 2) == 'd' || body.charAt(i + 2) == 'D')
					&&
					(body.charAt(i + 1) == '/')
					) {
						sb.append("\n");
						i = i + 6;
					} else if (
					(i + 7 < len)
					&&
					(body.charAt(i + 7) == '>')
					&&
					(body.charAt(i + 6) == 'e' || body.charAt(i + 6) == 'E')
					&&
					(body.charAt(i + 5) == 'l' || body.charAt(i + 5) == 'L')
					&&
					(body.charAt(i + 4) == 'b' || body.charAt(i + 4) == 'B')
					&&
					(body.charAt(i + 3) == 'a' || body.charAt(i + 3) == 'A')
					&&
					(body.charAt(i + 2) == 't' || body.charAt(i + 2) == 'T')
					&&
					(body.charAt(i + 1) == '/')
					) {
						sb.append("\n");
						i = i + 8;
					} else if (
					(i + 4 < len)
					&&
					(body.charAt(i + 4) == '>')
					&&
					(body.charAt(i + 3) == 'r' || body.charAt(i + 3) == 'R')
					&&
					(body.charAt(i + 2) == 't' || body.charAt(i + 2) == 'T')
					&&
					(body.charAt(i + 1) == '/')
					) {
						sb.append("\n");
						i = i + 5;
					} else if (
					(i + 3 < len)
					&&
					(body.charAt(i + 3) == '>')
					&&
					(body.charAt(i + 2) == 'i' || body.charAt(i + 2) == 'I')
					&&
					(body.charAt(i + 1) == 'l' || body.charAt(i + 1) == 'L')
					) {
						sb.append("\n");
						i = i + 4;
					} else {
						sb.append(c);
						i++;
					}
				} else if (!withInPreformat && Character.isWhitespace(c)) {
					sb.append(c);
					i++;
					// skip all following whitespaces
					while (i < len && Character.isWhitespace(body.charAt(i))) {
						i++;
					}
				} else {
					sb.append(c);
					i++;
				}
			}
			catch (Exception ex) {
				sb.append(body.substring(i));
				break;
			}
		}
		return sb.toString();
	}
}
