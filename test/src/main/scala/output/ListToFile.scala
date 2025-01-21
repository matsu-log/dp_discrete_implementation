package output
import java.io.PrintWriter

object ListToFile {
  def print(list: List[Int],fileName: String): Unit = {

    // PrintWriterを使用してファイルに書き込む
    val writer = new PrintWriter(fileName)

    // リストの要素をファイルに書き込む
    list.foreach(writer.println)

    // 書き込みが終わったらファイルを閉じる
    writer.close()

    println("ok")
  }
}