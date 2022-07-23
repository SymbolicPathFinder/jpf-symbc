package strings;
import java.util.InputMismatchException;
import java.util.Random;
import java.util.Scanner;
import java.io.File;


public class MasterMind {
	public static void main(String[] args){
		Random gen= new Random();
		int target= 0;
		while(hasDupes(target= (gen.nextInt(9000) + 1000)));
		String targetStr = target +"";
		String guessStr = "";
		boolean guessed = false;
		Scanner input = new Scanner(System.in);
		int guesses = 0;
		do{
			guessed = guessCode(guessStr, targetStr);
			guesses ++;
		}while(!guessed);
		System.out.println("You won after "+guesses+" guesses!");
	}

	public static boolean guessCode(String str, String target){
		int bulls = 0;
		int cows = 0;
		System.out.print("Guess a 4-digit number with no duplicate digits: ");
		int guess;
		try{
			guess = Integer.parseInt(str.trim());
			if(hasDupes(guess) || guess < 1000) return false;
		}catch(InputMismatchException e){
			return false;
		}
		String guessStr = guess + "";
		for(int i= 0;i < 4;i++){
			if(guessStr.charAt(i) == target.charAt(i)){
				bulls++;
			}else if(target.contains(guessStr.charAt(i)+"")){
				cows++;
			}
		}
		if(bulls == 4){
			return true;
		}else{
			System.out.println(cows+" Cows and "+bulls+" Bulls.");
		}

		return false;
	}
 
	public static boolean hasDupes(int num){
		boolean[] digs = new boolean[10];
		while(num > 0){
			if(digs[num%10]) return true;
			digs[num%10] = true;
			num/= 10;
		}
		return false;
	}
}
